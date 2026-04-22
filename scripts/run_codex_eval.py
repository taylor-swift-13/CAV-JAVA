#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "eval" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
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


def emit(message: str) -> None:
    print(f"[eval] {message}", flush=True)


def token_count(path: Path) -> int:
    if not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


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


def class_name_from_stem(stem: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in stem.replace("-", "_").split("_") if part)


def build_prompt(
    skill: Path,
    impl_java: Path,
    class_name: str,
    method_name: str,
    workspace: Path,
    harness_dir: Path,
    positive_harness: Path,
    negative_harness: Path,
) -> str:
    return f"""Use this skill as the complete workflow:
{skill}

Inputs:
- Implementation/spec Java: `{impl_java}`
- Target class: `{class_name}`
- Target method: `{method_name}`
- Workspace: `{workspace}`
- Harness directory: `{harness_dir}`
- Positive harness: `{positive_harness}`
- Negative harness: `{negative_harness}`

Rules:
- This eval stage is independent from contract and verify.
- Do not modify `{impl_java}`.
- Generate exactly 10 positive and 10 negative concrete harness cases.
- Positive harness must pass OpenJML.
- Negative harness must fail OpenJML for documented precondition/assertion reasons.
- Do not use assume, axiom, skipesc, nowarn, native, reflection, or unreachable-path tricks.
- Write logs under `{workspace / 'logs'}`.
"""


def run_scanner(java_file: Path, logs_dir: Path, label: str) -> int:
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts" / "check_jml_cheating.py"), str(java_file)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    (logs_dir / f"cheating_scan_stdout_{label}.log").write_text(proc.stdout, encoding="utf-8")
    (logs_dir / f"cheating_scan_stderr_{label}.log").write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def run_openjml(impl_java: Path, harness_java: Path, logs_dir: Path, label: str) -> int:
    proc = subprocess.run(
        [str(REPO_ROOT / "scripts" / "run_openjml_verify.sh"), str(impl_java), str(harness_java)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    (logs_dir / f"openjml_stdout_{label}.log").write_text(proc.stdout, encoding="utf-8")
    (logs_dir / f"openjml_stderr_{label}.log").write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def count_harness_cases(path: Path, prefix: str) -> int:
    if not path.exists():
        return 0
    text = path.read_text(encoding="utf-8", errors="replace")
    pattern = re.compile(rf"\b(?:public\s+)?(?:static\s+)?void\s+{re.escape(prefix)}\d{{2}}\w*\s*\(")
    return len(pattern.findall(text))


def write_placeholder_logs(logs_dir: Path, detail: str) -> None:
    (logs_dir / "test_reasoning.md").write_text(f"# Eval Reasoning\n\n{detail}\n", encoding="utf-8")
    (logs_dir / "issues.md").write_text("# Eval Issues\n\nNo issues recorded yet.\n", encoding="utf-8")


def append_issue(logs_dir: Path, title: str, detail: str) -> None:
    issues = logs_dir / "issues.md"
    existing = issues.read_text(encoding="utf-8") if issues.exists() else "# Eval Issues\n\n"
    issues.write_text(existing.rstrip() + f"\n\n## {title}\n\n{detail}\n", encoding="utf-8")


def write_final_result(
    path: Path,
    *,
    status: str,
    judgment: str,
    positive_count: int,
    negative_count: int,
    scan_impl: int | None,
    scan_positive: int | None,
    scan_negative: int | None,
    positive_openjml: int | None,
    negative_openjml: int | None,
) -> None:
    lines = [
        "# Eval Final Result",
        "",
        f"- Judgment: {judgment}",
        f"- Positive cases found: `{positive_count}`",
        f"- Negative cases found: `{negative_count}`",
        f"- Impl scan exit code: `{scan_impl if scan_impl is not None else 'not_run'}`",
        f"- Positive harness scan exit code: `{scan_positive if scan_positive is not None else 'not_run'}`",
        f"- Negative harness scan exit code: `{scan_negative if scan_negative is not None else 'not_run'}`",
        f"- Positive OpenJML exit code: `{positive_openjml if positive_openjml is not None else 'not_run'}`",
        f"- Negative OpenJML exit code: `{negative_openjml if negative_openjml is not None else 'not_run'}`",
        "",
        f"Final Result: {status}",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_metrics(
    path: Path,
    *,
    status: str,
    dry_run: bool,
    exit_code: int,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    model: str,
    reasoning_effort: str,
    impl_java: Path,
    positive_harness: Path,
    negative_harness: Path,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    usage: dict[str, int] | None,
    scan_impl: int | None,
    scan_positive: int | None,
    scan_negative: int | None,
    positive_openjml: int | None,
    negative_openjml: int | None,
    positive_count: int,
    negative_count: int,
    judgment: str,
) -> None:
    lines = [
        "# Eval Metrics",
        "",
        "- Stage: `eval`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Codex exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Implementation Java: `{impl_java}`",
        f"- Positive harness: `{positive_harness}`",
        f"- Negative harness: `{negative_harness}`",
        f"- Positive cases found: `{positive_count}`",
        f"- Negative cases found: `{negative_count}`",
        f"- Impl scan exit code: `{scan_impl if scan_impl is not None else 'not_run'}`",
        f"- Positive harness scan exit code: `{scan_positive if scan_positive is not None else 'not_run'}`",
        f"- Negative harness scan exit code: `{scan_negative if scan_negative is not None else 'not_run'}`",
        f"- Positive OpenJML exit code: `{positive_openjml if positive_openjml is not None else 'not_run'}`",
        f"- Negative OpenJML exit code: `{negative_openjml if negative_openjml is not None else 'not_run'}`",
        f"- Final judgment: `{judgment}`",
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
    parser = argparse.ArgumentParser(description="Run Codex for Java/OpenJML positive/negative eval generation.")
    parser.add_argument("impl_java", help="Path to implementation/spec Java file.")
    parser.add_argument("--class-name", help="Target class name. Defaults to PascalCase filename stem.")
    parser.add_argument("--method-name", help="Target method name. Defaults to filename stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to eval skill.")
    parser.add_argument("--workspace-name", help="Workspace/output stem. Defaults to input filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--codex-bin", default="codex")
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    impl_java = Path(args.impl_java)
    if not impl_java.is_absolute():
        impl_java = (REPO_ROOT / impl_java).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not impl_java.exists():
        print(f"implementation Java not found: {impl_java}", file=sys.stderr)
        return 2
    if impl_java.suffix != ".java":
        print(f"implementation file must be .java: {impl_java}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    stem = args.workspace_name or impl_java.stem
    timestamp = args.timestamp or timestamp_now()
    class_name = args.class_name or class_name_from_stem(stem)
    method_name = args.method_name or stem
    workspace = OUTPUT_ROOT / f"eval_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    harness_dir = workspace / "harness"
    original_dir = workspace / "original"
    logs_dir.mkdir(parents=True, exist_ok=True)
    harness_dir.mkdir(parents=True, exist_ok=True)
    original_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(impl_java, original_dir / impl_java.name)

    positive_harness = harness_dir / f"{class_name}PositiveHarness.java"
    negative_harness = harness_dir / f"{class_name}NegativeHarness.java"
    run_label = timestamp_now()
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"
    prompt = build_prompt(
        skill_path,
        impl_java,
        class_name,
        method_name,
        workspace,
        harness_dir,
        positive_harness,
        negative_harness,
    )
    prompt_path.write_text(prompt, encoding="utf-8")

    emit(f"workspace={workspace}")
    emit(f"impl_java={impl_java}")

    start = time.time()
    start_iso = iso_now()
    exit_code = 0
    scan_impl: int | None = None
    scan_positive: int | None = None
    scan_negative: int | None = None
    positive_openjml: int | None = None
    negative_openjml: int | None = None
    positive_count = 0
    negative_count = 0
    judgment = "Not fully tested."

    if args.dry_run:
        stdout_jsonl.write_text("", encoding="utf-8")
        stderr_log.write_text("", encoding="utf-8")
        last_message_path.write_text("Dry run: Codex was not invoked.\n", encoding="utf-8")
        write_placeholder_logs(logs_dir, "Dry run prepared the eval workspace and prompt; Codex was not invoked.")
        status = "Fail"
        judgment = "Dry run only; eval did not generate or prove the required 10 positive and 10 negative cases."
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

        scan_impl = run_scanner(impl_java, logs_dir, "impl")
        if positive_harness.exists():
            positive_count = count_harness_cases(positive_harness, "positive")
            scan_positive = run_scanner(positive_harness, logs_dir, "positive")
            if positive_count != 10:
                append_issue(
                    logs_dir,
                    "Incomplete positive cases",
                    f"Expected exactly 10 positive cases in `{positive_harness}`, found `{positive_count}`.",
                )
        else:
            append_issue(logs_dir, "Missing positive harness", f"Expected `{positive_harness}`.")
        if negative_harness.exists():
            negative_count = count_harness_cases(negative_harness, "negative")
            scan_negative = run_scanner(negative_harness, logs_dir, "negative")
            if negative_count != 10:
                append_issue(
                    logs_dir,
                    "Incomplete negative cases",
                    f"Expected exactly 10 negative cases in `{negative_harness}`, found `{negative_count}`.",
                )
        else:
            append_issue(logs_dir, "Missing negative harness", f"Expected `{negative_harness}`.")

        if scan_impl == 0 and scan_positive == 0 and positive_harness.exists() and positive_count == 10:
            positive_openjml = run_openjml(impl_java, positive_harness, logs_dir, "positive")
        if scan_impl == 0 and scan_negative == 0 and negative_harness.exists() and negative_count == 10:
            negative_openjml = run_openjml(impl_java, negative_harness, logs_dir, "negative")

        fully_tested = (
            exit_code == 0
            and positive_count == 10
            and negative_count == 10
            and scan_impl == 0
            and scan_positive == 0
            and scan_negative == 0
            and positive_openjml == 0
            and negative_openjml not in (None, 0)
        )
        status = "Success" if fully_tested else "Fail"
        if fully_tested:
            judgment = (
                "Eval completed: 10 positive cases were proved by OpenJML, "
                "and 10 negative cases produced expected spec-related OpenJML failures."
            )
        else:
            judgment = (
                "Eval incomplete or failed; Final Result cannot be Success until exactly "
                "10 positive and 10 negative cases are generated, scanned, and checked."
            )
        if not (logs_dir / "test_reasoning.md").exists():
            (logs_dir / "test_reasoning.md").write_text(
                "# Eval Reasoning\n\nNo eval reasoning log was produced.\n",
                encoding="utf-8",
            )
        if not (logs_dir / "issues.md").exists():
            (logs_dir / "issues.md").write_text("# Eval Issues\n\nNo issues recorded.\n", encoding="utf-8")

    usage = parse_usage(stdout_jsonl)
    end_iso = iso_now()
    write_metrics(
        logs_dir / "metrics.md",
        status=status,
        dry_run=args.dry_run,
        exit_code=exit_code,
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - start,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        impl_java=impl_java,
        positive_harness=positive_harness,
        negative_harness=negative_harness,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        usage=usage,
        scan_impl=scan_impl,
        scan_positive=scan_positive,
        scan_negative=scan_negative,
        positive_openjml=positive_openjml,
        negative_openjml=negative_openjml,
        positive_count=positive_count,
        negative_count=negative_count,
        judgment=judgment,
    )
    write_final_result(
        logs_dir / "final_result.md",
        status=status,
        judgment=judgment,
        positive_count=positive_count,
        negative_count=negative_count,
        scan_impl=scan_impl,
        scan_positive=scan_positive,
        scan_negative=scan_negative,
        positive_openjml=positive_openjml,
        negative_openjml=negative_openjml,
    )
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
