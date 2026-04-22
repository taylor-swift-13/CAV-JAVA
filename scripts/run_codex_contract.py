#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "contract" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_REASONING_EFFORT = "medium"
NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def token_count(path: Path) -> int:
    if not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


def emit(message: str) -> None:
    print(f"[contract] {message}", flush=True)


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".codex_cache",
        "XDG_STATE_HOME": ".state",
        "XDG_DATA_HOME": ".data",
        "XDG_CONFIG_HOME": ".config",
        "TMPDIR": ".tmp",
        "TMP": ".tmp",
        "TEMP": ".tmp",
    }.items():
        path = logs_dir / dirname
        path.mkdir(parents=True, exist_ok=True)
        env[name] = str(path)
    return env


def codex_supports_reasoning_effort(codex_bin: str, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=REPO_ROOT,
            env=env,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr(path: Path) -> None:
    if not path.exists():
        return
    kept = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in line for pattern in NOISE_PATTERNS):
            continue
        kept.append(line)
    path.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def parse_usage(stdout_jsonl: Path) -> dict[str, int] | None:
    if not stdout_jsonl.exists():
        return None
    usage = None
    for raw in stdout_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        if not raw.strip().startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if obj.get("type") == "turn.completed" and isinstance(obj.get("usage"), dict):
            usage = obj["usage"]
    return usage


def build_prompt(skill: Path, raw: Path, function_name: str, workspace: Path, target_java: Path) -> str:
    return f"""Use this skill as the complete workflow:
{skill}

Inputs:
- Raw markdown: `{raw}`
- Target function or class: `{function_name}`
- Workspace: `{workspace}`
- Output Java: `{target_java}`

Repository rules:
- This is Java/OpenJML, not C/Coq Verify.
- Before writing output, search `/home/yangfp/CAV-JAVA/experiences/end-end` for completed examples and reuse relevant patterns.
- Record any relevant completed example path in `{workspace / 'logs' / 'reasoning.md'}`.
- If this run produces a reusable lesson, update the relevant file under `/home/yangfp/CAV-JAVA/experiences/general`; otherwise record that no general update was needed.
- Write only Java/JML contract output in the contract stage.
- Do not use assume, axiom, skipesc, nowarn, native, or unchecked helpers.
- Write logs under `{workspace / 'logs'}`.
"""


def write_placeholder_logs(logs_dir: Path, stage: str, detail: str) -> None:
    (logs_dir / "reasoning.md").write_text(f"# {stage.title()} Reasoning\n\n{detail}\n", encoding="utf-8")
    (logs_dir / "issues.md").write_text(f"# {stage.title()} Issues\n\nNo issues recorded yet.\n", encoding="utf-8")


def write_metrics(
    path: Path,
    *,
    status: str,
    exit_code: int,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    model: str,
    reasoning_effort: str,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    target_java: Path,
    usage: dict[str, int] | None,
    scanner_exit: int | None,
    dry_run: bool,
) -> None:
    lines = [
        "# Contract Metrics",
        "",
        f"- Stage: `contract`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Output Java: `{target_java}`",
        f"- Anti-cheating scanner exit code: `{scanner_exit if scanner_exit is not None else 'not_run'}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Codex stdout JSONL: `{stdout_jsonl}`",
        f"- Codex stderr log: `{stderr_log}`",
        f"- Codex last message: `{last_message_path}`",
    ]
    if usage:
        for key in ("input_tokens", "cached_input_tokens", "output_tokens"):
            if key in usage:
                lines.append(f"- Codex CLI {key}: `{usage[key]}`")
    else:
        lines.append(f"- Approx prompt tokens: `{token_count(prompt_path)}`")
        lines.append(f"- Approx last-message tokens: `{token_count(last_message_path)}`")
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex for Java/OpenJML contract generation.")
    parser.add_argument("raw_md", help="Path to raw markdown task.")
    parser.add_argument("--function-name", required=True, help="Target method or class name.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to contract skill.")
    parser.add_argument("--workspace-name", help="Workspace/output stem. Defaults to raw filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--codex-bin", default="codex")
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    raw_path = Path(args.raw_md)
    if not raw_path.is_absolute():
        raw_path = (REPO_ROOT / raw_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not raw_path.exists():
        print(f"raw markdown not found: {raw_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    stem = args.workspace_name or raw_path.stem
    timestamp = args.timestamp or timestamp_now()
    workspace = OUTPUT_ROOT / f"contract_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    raw_dir = workspace / "raw"
    INPUT_ROOT.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)
    raw_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(raw_path, raw_dir / raw_path.name)

    target_java = INPUT_ROOT / f"{stem}.java"
    run_label = timestamp_now()
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"
    prompt = build_prompt(skill_path, raw_path, args.function_name, workspace, target_java)
    prompt_path.write_text(prompt, encoding="utf-8")

    emit(f"workspace={workspace}")
    emit(f"target_java={target_java}")

    start = time.time()
    start_iso = iso_now()
    exit_code = 0
    scanner_exit: int | None = None
    if args.dry_run:
        write_placeholder_logs(logs_dir, "contract", "Dry run prepared the workspace and prompt; Codex was not invoked.")
        last_message_path.write_text("Dry run: Codex was not invoked.\n", encoding="utf-8")
        stdout_jsonl.write_text("", encoding="utf-8")
        stderr_log.write_text("", encoding="utf-8")
        status = "Success"
    else:
        codex_env = build_codex_env(logs_dir)
        supports_effort = codex_supports_reasoning_effort(args.codex_bin, codex_env)
        cmd = [
            args.codex_bin,
            "--dangerously-bypass-approvals-and-sandbox",
            "exec",
            "--json",
            "--skip-git-repo-check",
            "-C",
            str(REPO_ROOT),
            "-o",
            str(last_message_path),
        ]
        if args.model:
            cmd.extend(["--model", args.model])
        if args.reasoning_effort and supports_effort:
            cmd.extend(["--reasoning-effort", args.reasoning_effort])
        cmd.append("-")
        try:
            with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
                proc = subprocess.run(
                    cmd,
                    input=prompt,
                    text=True,
                    stdout=out_f,
                    stderr=err_f,
                    cwd=REPO_ROOT,
                    env=codex_env,
                    timeout=args.timeout_seconds,
                )
            exit_code = proc.returncode
        except subprocess.TimeoutExpired:
            exit_code = 124
            stderr_log.write_text("Codex execution timed out.\n", encoding="utf-8")
        filter_stderr(stderr_log)

        if exit_code == 0 and target_java.exists():
            scanner = subprocess.run(
                [sys.executable, str(REPO_ROOT / "scripts" / "check_jml_cheating.py"), str(target_java)],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                cwd=REPO_ROOT,
            )
            scanner_exit = scanner.returncode
            (logs_dir / "cheating_scan_stdout.log").write_text(scanner.stdout, encoding="utf-8")
            (logs_dir / "cheating_scan_stderr.log").write_text(scanner.stderr, encoding="utf-8")
        status = "Success" if exit_code == 0 and target_java.exists() and scanner_exit == 0 else "Fail"
        if not (logs_dir / "issues.md").exists():
            detail = "No issues recorded by Codex." if status == "Success" else "Contract did not complete successfully."
            (logs_dir / "issues.md").write_text(f"# Contract Issues\n\n{detail}\n", encoding="utf-8")
        if not (logs_dir / "reasoning.md").exists():
            (logs_dir / "reasoning.md").write_text("# Contract Reasoning\n\nNo reasoning log was produced.\n", encoding="utf-8")

    end_iso = iso_now()
    usage = parse_usage(stdout_jsonl)
    write_metrics(
        logs_dir / "metrics.md",
        status=status,
        exit_code=exit_code,
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - start,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        target_java=target_java,
        usage=usage,
        scanner_exit=scanner_exit,
        dry_run=args.dry_run,
    )
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
