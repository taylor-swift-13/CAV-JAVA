#!/usr/bin/env python3
import argparse
import datetime as dt
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import check_spec_wellformed


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "contract" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
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


def emit_log(message: str) -> None:
    print(f"[contract] {message}", flush=True)


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    cache_dir = logs_dir / ".codex_cache"
    state_dir = logs_dir / ".state"
    data_dir = logs_dir / ".data"
    config_dir = logs_dir / ".config"
    tmp_dir = logs_dir / ".tmp"
    cache_dir.mkdir(parents=True, exist_ok=True)
    state_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    config_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    env["XDG_CACHE_HOME"] = str(cache_dir)
    env["XDG_STATE_HOME"] = str(state_dir)
    env["XDG_DATA_HOME"] = str(data_dir)
    env["XDG_CONFIG_HOME"] = str(config_dir)
    env["TMPDIR"] = str(tmp_dir)
    env["TMP"] = str(tmp_dir)
    env["TEMP"] = str(tmp_dir)
    return env


def codex_supports_reasoning_effort(codex_bin: str, cwd: Path, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=cwd,
            env=env,
            timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    clean_lines = []
    for raw_line in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in raw_line for pattern in NOISE_PATTERNS):
            continue
        clean_lines.append(raw_line)
    stderr_log.write_text("\n".join(clean_lines) + ("\n" if clean_lines else ""), encoding="utf-8")


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


def issues_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "issues.md"


def reasoning_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "reasoning.md"


def bootstrap_workspace(workspace_path: Path, raw_path: Path) -> dict[str, Path]:
    logs_dir = workspace_path / "logs"
    raw_dir = workspace_path / "raw"
    workspace_input_dir = workspace_path / "input"
    logs_dir.mkdir(parents=True, exist_ok=True)
    raw_dir.mkdir(parents=True, exist_ok=True)
    workspace_input_dir.mkdir(parents=True, exist_ok=True)

    raw_copy = raw_dir / raw_path.name
    shutil.copy2(raw_path, raw_copy)
    return {
        "logs_dir": logs_dir,
        "raw_dir": raw_dir,
        "workspace_input_dir": workspace_input_dir,
        "raw_copy": raw_copy,
    }


def build_prompt(
    skill_path: Path,
    raw_path: Path,
    workspace_path: Path,
    target_c_path: Path,
    target_v_path: Path,
    function_name: str,
    restart_context: str | None = None,
) -> str:
    restart = ""
    if restart_context:
        restart = (
            "\nThis is a RE-RUN: a downstream eval critic rejected the previous "
            "contract. Address its findings before re-emitting the contract.\n\n"
            "Critic findings:\n" + restart_context.rstrip() + "\n"
        )
    return f"""Use this skill as the complete workflow:
{skill_path}

Inputs:
- Raw markdown: `{raw_path}`
- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Output C: `{target_c_path}`
- Optional output V: `{target_v_path}`
{restart}"""


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
    target_c: Path,
    target_v: Path,
    usage: dict[str, int] | None,
    dry_run: bool,
    wellformed: str = "not_run",
    wellformed_exit: int | None = None,
) -> None:
    lines = [
        "# Contract Metrics",
        "",
        "- Stage: `contract`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Output C: `{target_c}`",
        f"- Output V: `{target_v if target_v.exists() else '<not created>'}`",
        f"- Spec well-formedness gate: `{wellformed}` (symexec exit `{wellformed_exit if wellformed_exit is not None else 'n/a'}`)",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_md: Path, stage: str, exit_code: int, stderr_log: Path, detail: str | None = None) -> None:
    issues_md.parent.mkdir(parents=True, exist_ok=True)
    if issues_md.exists():
        existing = issues_md.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Contract Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    if detail:
        block += f"- Detail: `{detail}`\n"
    issues_md.write_text(existing + block, encoding="utf-8")


def ensure_reasoning_placeholder(reasoning_md: Path, stage: str, detail: str | None = None) -> None:
    if reasoning_md.exists():
        return
    lines = [
        "# Contract Reasoning",
        "",
        "## Unavailable",
        "",
        f"- This file was not produced by the contract run because stage `{stage}` failed before reasoning was written.",
    ]
    if detail:
        lines.append(f"- Failure detail: `{detail}`")
    reasoning_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


def snapshot_generated_inputs(workspace_path: Path, input_c: Path, input_v: Path) -> None:
    generated_input_dir = workspace_path / "input"
    generated_input_dir.mkdir(parents=True, exist_ok=True)
    if input_c.exists():
        shutil.copy2(input_c, generated_input_dir / input_c.name)
    if input_v.exists():
        shutil.copy2(input_v, generated_input_dir / input_v.name)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to produce contract-stage inputs from raw markdown.")
    parser.add_argument("input_md", help="Path to raw markdown input, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional target function name. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Explicit target function name. Defaults to markdown stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to contract skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to markdown stem.")
    parser.add_argument("--timestamp", help="Explicit contract timestamp; defaults to current local time.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude"], default=None)
    parser.add_argument("--model", default=None, help="Agent model.")
    parser.add_argument("--reasoning-effort", default=None, help="Agent reasoning effort.")
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=300, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. eval critic findings) is injected into the prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    raw_path = Path(args.input_md)
    if not raw_path.is_absolute():
        raw_path = (REPO_ROOT / raw_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not raw_path.exists():
        print(f"input markdown not found: {raw_path}", file=sys.stderr)
        return 2
    if raw_path.suffix != ".md":
        print(f"input markdown must be a .md file: {raw_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.default_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")

    workspace_stem = args.workspace_name or raw_path.stem
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"contract_{workspace_timestamp}_{workspace_stem}"
    bootstrap_workspace(workspace_path, raw_path)
    emit_log(f"workspace={workspace_path}")

    function_name = args.function_name or args.function_name_positional or raw_path.stem
    target_c_path = INPUT_ROOT / f"{raw_path.stem}.c"
    target_v_path = INPUT_ROOT / f"{raw_path.stem}.v"
    emit_log(f"input_md={raw_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"target_c={target_c_path}")
    emit_log(f"target_v={target_v_path}")

    logs_dir = workspace_path / "logs"
    codex_env = build_codex_env(logs_dir)
    reasoning_effort_supported = codex_supports_reasoning_effort(codex_bin, REPO_ROOT, codex_env)
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"

    restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            restart_context = rc_path.read_text(encoding="utf-8", errors="replace")
    prompt = build_prompt(
        skill_path,
        raw_path,
        workspace_path,
        target_c_path,
        target_v_path,
        function_name,
        restart_context,
    )
    ensure_parent(prompt_path)
    prompt_path.write_text(prompt, encoding="utf-8")

    if args.dry_run:
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            exit_code=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_seconds=0.0,
            model=model,
            reasoning_effort=reasoning_effort,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            target_c=target_c_path,
            target_v=target_v_path,
            usage=None,
            dry_run=True,
        )
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    emit_log(f"agent_exec_start timeout_seconds={args.timeout_seconds}")

    proc_returncode = 0
    status = "Fail"
    failure_detail = None
    try:
        if agent == "claude":
            cmd = [
                claude_bin,
                "--print",
                "--dangerously-skip-permissions",
                "--add-dir",
                str(REPO_ROOT),
                "--output-format",
                "stream-json",
                "--verbose",
            ]
            if model:
                cmd.extend(["--model", model])
            with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
                proc = subprocess.run(
                    cmd,
                    input=prompt,
                    text=True,
                    stdout=out_f,
                    stderr=err_f,
                    cwd=REPO_ROOT,
                    timeout=args.timeout_seconds,
                    env=codex_env,
                )
            proc_returncode = proc.returncode
            last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
            if last_message is not None:
                last_message_path.write_text(last_message, encoding="utf-8")
            elif stdout_jsonl.exists():
                last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
        else:
            cmd = [
                codex_bin,
                "--dangerously-bypass-approvals-and-sandbox",
                "exec",
                "--json",
                "--skip-git-repo-check",
                "-C",
                str(REPO_ROOT),
                "-o",
                str(last_message_path),
            ]
            if model:
                cmd.extend(["--model", model])
            if reasoning_effort and reasoning_effort_supported:
                cmd.extend(["--reasoning-effort", reasoning_effort])
            cmd.append("-")
            with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
                proc = subprocess.run(
                    cmd,
                    input=prompt,
                    text=True,
                    stdout=out_f,
                    stderr=err_f,
                    cwd=REPO_ROOT,
                    timeout=args.timeout_seconds,
                    env=codex_env,
                )
            proc_returncode = proc.returncode
    except subprocess.TimeoutExpired:
        proc_returncode = 124
        failure_detail = f"external agent run exceeded timeout of {args.timeout_seconds} seconds"
        emit_log(f"agent_exec_timeout detail={failure_detail}")
    end_wall = time.time()
    end_iso = iso_now()
    filter_stderr_in_place(stderr_log)

    snapshot_generated_inputs(workspace_path, target_c_path, target_v_path)

    usage = agent_metrics.parse_usage(agent, stdout_jsonl)
    if proc_returncode == 0:
        status = "Success"

    # Contract well-formedness gate: tolerant, recorded only (never blocks).
    wellformed, wellformed_exit = "not_run", None
    if target_c_path.exists():
        try:
            wellformed, wellformed_exit, wf_detail = check_spec_wellformed.check(target_c_path)
            emit_log(f"wellformed={wellformed} symexec_exit={wellformed_exit} detail={wf_detail}")
        except Exception as exc:  # noqa: BLE001 - gate is best-effort
            emit_log(f"wellformed_check_failed: {exc}")

    write_metrics(
        metrics_path(workspace_path),
        status=status,
        exit_code=proc_returncode,
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=end_wall - start_wall,
        model=model,
        reasoning_effort=reasoning_effort,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        target_c=target_c_path,
        target_v=target_v_path,
        usage=usage,
        dry_run=False,
        wellformed=wellformed,
        wellformed_exit=wellformed_exit,
    )

    if proc_returncode != 0:
        ensure_reasoning_placeholder(
            reasoning_path(workspace_path),
            "external-codex-run",
            failure_detail,
        )
        update_issues_on_failure(
            issues_path(workspace_path),
            "external-codex-run",
            proc_returncode,
            stderr_log,
            failure_detail,
        )
        emit_log(f"agent_exec_failed exit_code={proc_returncode}")
    else:
        emit_log("agent_exec_completed exit_code=0")

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


if __name__ == "__main__":
    sys.exit(main())
