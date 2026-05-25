#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics


REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
EXAMPLES_ROOT = REPO_ROOT / "experiences" / "end-end"
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


def stem_from_input(input_path: Path) -> str:
    return input_path.stem


def sha256_hex(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def emit_log(message: str) -> None:
    print(f"[verify] {message}", flush=True)


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


def paired_input_v(input_path: Path) -> Path | None:
    candidate = input_path.with_suffix(".v")
    if candidate.exists():
        return candidate
    return None


def build_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    input_v_line = f"- Optional input V: `{input_v_path}`\n" if input_v_path else "- Optional input V: `<not provided>`\n"
    continue_path = workspace_path / "logs" / "continue.md"
    if attempt <= 1:
        restart = ""
        if restart_context:
            restart = (
                "\nThis verify is a RE-RUN after an audit critic flagged the "
                "previous attempt as untrustworthy. Address every finding below — "
                "in particular, do NOT leave any obligation `Admitted.` in "
                "proof_auto.v or proof_manual.v.\n\nAudit findings:\n"
                + restart_context.rstrip() + "\n"
            )
        return f"""Use this skill as the complete workflow:
{skill_path}

Inputs:
- Input C: `{input_path}`
{input_v_line}- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Active annotated C: `{annotated_c_path}`
{restart}
Execution rule:
- Work only inside this existing workspace.
- Start from the normal verify workflow for this task.
- Early in the task, read `doc/retrieval/INDEX.md`, then update `logs/workspace_fingerprint.json` so `semantic_description` is non-empty and `keywords` use only the controlled vocabulary defined there.
- Keep iterating in the same workspace until verification succeeds or the external time budget is exhausted.
"""
    return f"""Use this skill as the complete workflow:
{skill_path}

Retry round for the same verify workspace.

Inputs:
- Input C: `{input_path}`
{input_v_line}- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Active annotated C: `{annotated_c_path}`
- Continue analysis log: `{continue_path}`

Retry rule:
- Do not restart the task from scratch.
- First read the current logs, generated Coq files, latest compile errors, latest `codex_last_message_*`, latest `codex_stderr_*`, and current annotated file in this workspace.
- Before editing any file, append a new section to `logs/continue.md`; never overwrite or rewrite existing `continue.md` content.
- Every retry round must keep extending `logs/continue.md` with a fresh section for that round, even if an earlier retry already wrote one.
- In the new `logs/continue.md` section, analyze why the previous agent/run did not finish, what concrete blocker remains now, what should be continued next, how to do it, and the step-by-step plan for this retry.
- The continue analysis must cite concrete workspace evidence: file paths, theorem/witness names, compile errors, relevant C annotation snippets, or relevant Coq snippets. Do not write only generic text.
- If `logs/workspace_fingerprint.json` still has empty `semantic_description` or `keywords`, first read `doc/retrieval/INDEX.md` and fill them using only its controlled vocabulary before proceeding.
- Precisely identify the current blocker from the existing workspace state.
- Continue repairing from that blocker in the same workspace.
- Preserve existing correct work; only change what is needed for the next proof/compile step.
- Keep iterating until verification succeeds or the external time budget is exhausted.
"""


def write_metrics(
    metrics_md_path: Path,
    *,
    status: str,
    attempts: int,
    last_agent_exit: int,
    start_iso: str,
    end_iso: str,
    wall_clock_seconds: float,
    model: str,
    reasoning_effort: str,
    usage: dict[str, int] | None,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    input_c: Path,
    input_v: Path | None,
    export_examples: bool,
) -> None:
    lines = [
        "# Verify Metrics",
        "",
        "- Stage: `verify`",
        f"- Status: `{status}`",
        f"- Attempts: `{attempts}`",
        f"- Last agent exit code: `{last_agent_exit}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_clock_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Input C: `{input_c}`",
        f"- Input V: `{input_v if input_v else '<not provided>'}`",
        f"- Export examples: `{str(export_examples).lower()}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    metrics_md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_path: Path, stage: str, exit_code: int, stderr_log: Path) -> None:
    issues_path.parent.mkdir(parents=True, exist_ok=True)
    if issues_path.exists():
        existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Execution Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    issues_path.write_text(existing + block, encoding="utf-8")


def verify_workspace_completed(workspace_path: Path) -> tuple[bool, str]:
    metrics_md = metrics_path(workspace_path)
    if not metrics_md.exists():
        return False, f"missing_metrics:{metrics_md}"

    lines = metrics_md.read_text(encoding="utf-8", errors="replace").splitlines()
    saw_success = False
    saw_fail = False
    for raw_line in lines:
        line = raw_line.strip()
        if line == "Final Result: Success":
            saw_success = True
        elif line == "Final Result: Fail":
            saw_fail = True

    if saw_success:
        return True, "metrics_contains_final_result_success"
    if saw_fail:
        return False, "metrics_contains_final_result_fail"
    return False, "metrics_missing_final_result"


def copy_if_exists(src: Path, dst: Path) -> None:
    if not src.exists():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def export_example_if_needed(workspace_path: Path, function_name: str) -> tuple[bool, str]:
    """On verify success, copy the workspace into experiences/end-end/<name>/.

    Inlined here (the Java pipeline does the same in run_verify); keeps only the
    .v / .c / reasoning artifacts, never the compile intermediates.
    """
    target_dir = EXAMPLES_ROOT / function_name
    if target_dir.exists():
        return False, f"skip_existing:{target_dir}"
    completed, detail = verify_workspace_completed(workspace_path)
    if not completed:
        return False, f"skip_incomplete_verify:{detail}"
    generated_dir = workspace_path / "coq" / "generated"
    if not (generated_dir / f"{function_name}_proof_manual.v").exists():
        return False, f"missing_proof_manual:{generated_dir}/{function_name}_proof_manual.v"

    target_dir.mkdir(parents=True, exist_ok=True)
    original_dir = workspace_path / "original"
    logs_dir = workspace_path / "logs"
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"

    copy_if_exists(original_dir / f"{function_name}.c", target_dir / "original" / f"{function_name}.c")
    copy_if_exists(original_dir / f"{function_name}.v", target_dir / "original" / f"{function_name}.v")
    copy_if_exists(annotated_c, target_dir / "annotated" / f"{function_name}.c")
    for src in sorted(generated_dir.glob("*.v")):
        copy_if_exists(src, target_dir / "coq" / "generated" / src.name)
    for fname in ("workspace_fingerprint.json", "annotation_reasoning.md", "proof_reasoning.md", "issues.md"):
        copy_if_exists(logs_dir / fname, target_dir / "logs" / fname)

    # Keep only sources: drop any copied compile intermediates and the metrics file.
    coq_runner.clean_compile_artifacts(target_dir)
    metrics = target_dir / "logs" / "metrics.md"
    if metrics.exists():
        metrics.unlink()
    return True, target_dir.as_posix()


def bootstrap_workspace(workspace_path: Path, input_path: Path, input_v_path: Path | None, function_name: str) -> Path:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    (workspace_path / "coq").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "annotated").mkdir(parents=True, exist_ok=True)

    original_c = workspace_path / "original" / input_path.name
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"
    shutil.copy2(input_path, original_c)
    shutil.copy2(input_path, annotated_c)

    original_v = ""
    if input_v_path is not None:
        dst_v = workspace_path / "original" / input_v_path.name
        shutil.copy2(input_v_path, dst_v)
        original_v = str(dst_v)

    fingerprint_path = workspace_path / "logs" / "workspace_fingerprint.json"
    fingerprint = {
        "fingerprint_version": 2,
        "workspace": workspace_path.name,
        "stage": "verify",
        "input_c": str(input_path),
        "input_v": str(input_v_path) if input_v_path else "",
        "original_c": str(original_c),
        "original_v": original_v,
        "annotated_c": str(annotated_c),
        "function_name": function_name,
        "program_sha256": sha256_hex(input_path),
        "semantic_description": "",
        "keywords": {},
        "assume_contract_is_correct": True,
        "contract_source": "contract_input_c",
    }
    fingerprint_path.write_text(json.dumps(fingerprint, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return annotated_c


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to execute the full verify workflow.")
    parser.add_argument("input_c", help="Path to input C file, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional function name to verify. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Function name to verify. Preferred form.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to verification skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit verify timestamp; defaults to current local time.")
    parser.add_argument("--model", default=None, help="Agent model. Defaults to config, else built-in per agent.")
    parser.add_argument(
        "--reasoning-effort",
        default=None,
        help="Agent reasoning effort. Defaults to config, else medium.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument(
        "--export-examples",
        action="store_true",
        help="If verify succeeds, export the workspace into experiences/end-end/<function_name>/ unless that example already exists.",
    )
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude"], default=None)
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=3600, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. audit critic findings) is injected into the round-1 prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.default_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")

    input_path = Path(args.input_c)
    if not input_path.is_absolute():
        input_path = (REPO_ROOT / input_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not input_path.exists():
        print(f"input file not found: {input_path}", file=sys.stderr)
        return 2
    if input_path.suffix != ".c":
        print(f"input file must be a .c file: {input_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    function_name = args.function_name or args.function_name_positional
    if not function_name:
        print("function name is required: pass --function-name NAME or a positional NAME", file=sys.stderr)
        return 2

    input_v_path = paired_input_v(input_path)

    workspace_stem = args.workspace_name or stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"verify_{workspace_timestamp}_{workspace_stem}"
    annotated_c_path = bootstrap_workspace(workspace_path, input_path, input_v_path, function_name)
    emit_log(f"workspace={workspace_path}")
    emit_log(f"input_c={input_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"input_v={input_v_path if input_v_path else '<not provided>'}")
    emit_log(f"annotated_c={annotated_c_path}")
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    logs_dir = workspace_path / "logs"
    codex_env = build_codex_env(logs_dir)
    reasoning_effort_supported = codex_supports_reasoning_effort(codex_bin, REPO_ROOT, codex_env)
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"

    if args.dry_run:
        prompt = build_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path, 1)
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            attempts=0,
            last_agent_exit=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_clock_seconds=0.0,
            model=model,
            reasoning_effort=reasoning_effort,
            usage=None,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            input_c=input_path,
            input_v=input_v_path,
            export_examples=args.export_examples,
        )
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    total_budget_seconds = args.timeout_seconds
    overall_start_wall = time.time()
    overall_start_iso = iso_now()
    attempt = 0
    proc_returncode = 1
    completed = False
    usage_total: dict[str, int] | None = None

    verify_restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            verify_restart_context = rc_path.read_text(encoding="utf-8", errors="replace")

    while True:
        attempt += 1
        elapsed_before = time.time() - overall_start_wall
        remaining_budget = total_budget_seconds - elapsed_before
        if remaining_budget <= 0:
            emit_log("codex_exec_budget_exhausted")
            proc_returncode = 124
            break

        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
        stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
        stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
        last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"
        prompt = build_prompt(
            skill_path,
            input_path,
            input_v_path,
            function_name,
            workspace_path,
            annotated_c_path,
            attempt,
            verify_restart_context,
        )
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")

        round_timeout = max(1, int(remaining_budget))
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
        emit_log(
            f"agent_exec_start attempt={attempt} round_timeout_seconds={round_timeout} total_budget_seconds={total_budget_seconds}"
        )

        start_wall = time.time()
        start_iso = iso_now()
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
                        timeout=round_timeout,
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
                        timeout=round_timeout,
                        env=codex_env,
                    )
                proc_returncode = proc.returncode
        except subprocess.TimeoutExpired:
            proc_returncode = 124
            failure_detail = f"external agent run exceeded remaining timeout budget of {round_timeout} seconds"
            emit_log(f"agent_exec_timeout attempt={attempt} detail={failure_detail}")
        end_wall = time.time()
        filter_stderr_in_place(stderr_log)

        usage_total = agent_metrics.add_usage(usage_total, agent_metrics.parse_usage(agent, stdout_jsonl))

        if proc_returncode != 0:
            update_issues_on_failure(
                workspace_path / "logs" / "issues.md",
                "external-codex-run",
                proc_returncode,
                stderr_log,
            )
            if failure_detail is not None:
                issues_path = workspace_path / "logs" / "issues.md"
                existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n"
                issues_path.write_text(existing + f"- Detail: `{failure_detail}`\n", encoding="utf-8")
            emit_log(f"agent_exec_failed attempt={attempt} exit_code={proc_returncode}")
        else:
            emit_log(f"agent_exec_completed attempt={attempt} exit_code=0")

        completed, detail = verify_workspace_completed(workspace_path)
        if completed:
            emit_log(f"verify_completed={detail}")
            if args.export_examples:
                exported, export_detail = export_example_if_needed(workspace_path, function_name)
                if exported:
                    emit_log(f"examples_exported={export_detail}")
                else:
                    emit_log(f"examples_export_skipped={export_detail}")
            proc_returncode = 0
            break

        elapsed_total = time.time() - overall_start_wall
        if elapsed_total >= total_budget_seconds:
            emit_log("codex_exec_budget_exhausted_after_attempt")
            if proc_returncode == 0:
                proc_returncode = 124
            break

        emit_log(
            f"verify_incomplete_retrying attempt={attempt} detail={detail} remaining_seconds={max(0, int(total_budget_seconds - elapsed_total))}"
        )

    # COMPILE.md §10: drop coqc intermediates (.vo/.glob/.aux) from the
    # workspace coq dirs, keeping .v sources. Never touches the shared QCP tree.
    removed = coq_runner.clean_compile_artifacts(workspace_path / "coq")
    emit_log(f"cleaned_compile_artifacts count={len(removed)}")

    overall_end_iso = iso_now()
    write_metrics(
        metrics_path(workspace_path),
        status="Success" if proc_returncode == 0 else "Fail",
        attempts=attempt,
        last_agent_exit=proc_returncode,
        start_iso=overall_start_iso,
        end_iso=overall_end_iso,
        wall_clock_seconds=time.time() - overall_start_wall,
        model=model,
        reasoning_effort=reasoning_effort,
        usage=usage_total,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        input_c=input_path,
        input_v=input_v_path,
        export_examples=args.export_examples,
    )

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


if __name__ == "__main__":
    sys.exit(main())
