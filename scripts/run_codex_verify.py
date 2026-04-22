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
DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
EXPERIENCES_ROOT = REPO_ROOT / "experiences" / "end-end"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_REASONING_EFFORT = "medium"
NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]
CONTROLLED_KEYWORDS = {
    "algorithm_family": {
        "identity",
        "selection",
        "counting",
        "accumulation",
        "arithmetic_series",
        "factorial",
        "prefix_sum",
        "simulation",
        "search",
        "two_pointers",
        "dynamic_programming",
        "greedy",
        "recursion",
    },
    "control_flow": {
        "straight_line",
        "if",
        "ternary",
        "for_loop",
        "while_loop",
        "do_while",
        "nested_loop",
        "recursion",
    },
    "data_shape": {
        "scalar_only",
        "array",
        "string",
        "pointer",
        "struct",
        "linked_list",
        "tree",
        "graph",
    },
    "semantic_intent": {
        "return_input",
        "return_max",
        "count_iterations",
        "sum_1_to_n",
        "sum_even_series",
        "compute_factorial",
        "preserve_input",
        "in_place_update",
    },
    "proof_pattern": {
        "pure_arithmetic",
        "loop_invariant",
        "case_split",
        "termination_by_bound",
        "closed_form",
        "monotonicity",
        "range_bound",
        "heap_reasoning",
    },
    "numeric_properties": {
        "nonnegative_input",
        "overflow_guard",
        "int_range",
        "monotone_accumulator",
        "exact_closed_form",
    },
    "edge_case_behavior": {
        "returns_zero_on_nonpositive",
        "returns_input_on_nonpositive",
        "defined_for_nonnegative_only",
        "branch_on_order",
        "empty_loop_possible",
    },
    "verification_status": {
        "goal_check_passed",
        "proof_check_passed",
        "manual_witness_needed",
        "auto_proof_contains_admitted",
        "generated_goal_contains_axioms",
    },
}


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def emit(message: str) -> None:
    print(f"[verify] {message}", flush=True)


def token_count(path: Path) -> int:
    if not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


def sha256(path: Path) -> str:
    import hashlib

    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    original_java: Path,
    verified_java: Path,
    workspace: Path,
    class_name: str,
    attempt: int,
) -> str:
    if attempt == 1:
        intro = "Start the normal Java/OpenJML verify workflow for this task."
    else:
        intro = "Retry in the same workspace. Read existing logs first and continue from the current blocker."
    return f"""Use this skill as the complete workflow:
{skill}

{intro}

Inputs:
- Original Java: `{original_java}`
- Verified working Java: `{verified_java}`
- Workspace: `{workspace}`
- Class name: `{class_name}`

Hard success gate:
- Before editing, search `/home/yangfp/CAV-JAVA/experiences/end-end` for completed examples with similar Java/JML patterns.
- Read `/home/yangfp/CAV-JAVA/experiences/INDEX.md`, then fill `{workspace / 'logs' / 'workspace_fingerprint.json'}` with a non-empty `semantic_description` and non-empty controlled `keywords`.
- Record any relevant completed example path in `{workspace / 'logs' / 'annotation_reasoning.md'}`.
- If this run produces a reusable lesson, update the relevant file under `/home/yangfp/CAV-JAVA/experiences/general`; otherwise record that no general update was needed.
- Preserve baseline contract clauses from the original Java file.
- Do not use assume, axiom, Admitted, skipesc, nowarn, native, reflection, or unchecked helpers.
- Run `scripts/check_jml_cheating.py --baseline {original_java} {verified_java}`.
- Run `scripts/run_openjml_verify.sh {verified_java}`.
- Only report success if both commands pass.
"""


def validate_fingerprint(workspace: Path) -> tuple[bool, str]:
    path = workspace / "logs" / "workspace_fingerprint.json"
    if not path.exists():
        return False, f"missing fingerprint: {path}"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return False, f"fingerprint is not valid JSON: {exc}"

    description = data.get("semantic_description")
    if not isinstance(description, str) or not description.strip():
        return False, "fingerprint semantic_description must be non-empty"

    keywords = data.get("keywords")
    if not isinstance(keywords, dict) or not keywords:
        return False, "fingerprint keywords must be a non-empty object"

    for key, value in keywords.items():
        allowed_values = CONTROLLED_KEYWORDS.get(key)
        if allowed_values is None:
            return False, f"fingerprint keyword key is not controlled: {key}"
        values = value if isinstance(value, list) else [value]
        if not values:
            return False, f"fingerprint keyword list is empty: {key}"
        for item in values:
            if not isinstance(item, str):
                return False, f"fingerprint keyword value for {key} is not a string: {item!r}"
            if item not in allowed_values:
                return False, f"fingerprint keyword value for {key} is not controlled: {item}"
    return True, "ok"


def write_fingerprint(
    workspace: Path,
    input_java: Path,
    original_java: Path,
    verified_java: Path,
    class_name: str,
) -> None:
    data = {
        "fingerprint_version": 2,
        "workspace": workspace.name,
        "stage": "verify",
        "input_java": str(input_java),
        "original_java": str(original_java),
        "verified_java": str(verified_java),
        "class_name": class_name,
        "program_sha256": sha256(input_java),
        "semantic_description": "",
        "keywords": {},
        "assume_contract_is_correct": True,
        "contract_source": "contract_input_java",
        "anti_cheating_required": True,
        "openjml_required": True,
    }
    (workspace / "logs" / "workspace_fingerprint.json").write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def parse_workspace_name(workspace: Path) -> str:
    name = workspace.name
    if not name.startswith("verify_"):
        raise ValueError(f"workspace basename must start with 'verify_': {name}")
    parts = name.split("_", 3)
    if len(parts) < 4:
        raise ValueError(f"workspace basename must match verify_<timestamp>_<name>: {name}")
    return parts[3]


def copy_if_exists(src: Path, dst: Path) -> None:
    if not src.exists():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def verify_workspace_completed(workspace: Path) -> tuple[bool, str]:
    metrics = workspace / "logs" / "metrics.md"
    if not metrics.exists():
        return False, f"missing_metrics:{metrics}"
    saw_success = False
    saw_fail = False
    for raw_line in metrics.read_text(encoding="utf-8", errors="replace").splitlines():
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


def export_experience_if_needed(workspace: Path) -> tuple[bool, str]:
    name = parse_workspace_name(workspace)
    dst_root = EXPERIENCES_ROOT / name
    if dst_root.exists():
        return False, f"skip_existing:{dst_root}"
    completed, detail = verify_workspace_completed(workspace)
    if not completed:
        return False, f"skip_incomplete_verify:{detail}"
    dst_root.mkdir(parents=True, exist_ok=True)

    original_dir = workspace / "original"
    verified_dir = workspace / "verified"
    logs_dir = workspace / "logs"

    copy_if_exists(original_dir / f"{name}.java", dst_root / "original" / f"{name}.java")
    copy_if_exists(verified_dir / f"{name}.java", dst_root / "verified" / f"{name}.java")
    copy_if_exists(logs_dir / "workspace_fingerprint.json", dst_root / "logs" / "workspace_fingerprint.json")
    copy_if_exists(logs_dir / "annotation_reasoning.md", dst_root / "logs" / "annotation_reasoning.md")
    copy_if_exists(logs_dir / "issues.md", dst_root / "logs" / "issues.md")

    return True, dst_root.as_posix()


def append_issue(logs_dir: Path, title: str, detail: str) -> None:
    issues = logs_dir / "issues.md"
    existing = issues.read_text(encoding="utf-8") if issues.exists() else "# Verify Issues\n\n"
    issues.write_text(existing.rstrip() + f"\n\n## {title}\n\n{detail}\n", encoding="utf-8")


def run_scanner(original_java: Path, verified_java: Path, logs_dir: Path, label: str) -> int:
    stdout = logs_dir / f"cheating_scan_stdout_{label}.log"
    stderr = logs_dir / f"cheating_scan_stderr_{label}.log"
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "check_jml_cheating.py"),
            "--baseline",
            str(original_java),
            str(verified_java),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    stdout.write_text(proc.stdout, encoding="utf-8")
    stderr.write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def run_openjml(verified_java: Path, logs_dir: Path, label: str) -> int:
    stdout = logs_dir / f"openjml_stdout_{label}.log"
    stderr = logs_dir / f"openjml_stderr_{label}.log"
    proc = subprocess.run(
        [str(REPO_ROOT / "scripts" / "run_openjml_verify.sh"), str(verified_java)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    stdout.write_text(proc.stdout, encoding="utf-8")
    stderr.write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def write_metrics(
    path: Path,
    *,
    status: str,
    dry_run: bool,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    model: str,
    reasoning_effort: str,
    attempts: int,
    last_codex_exit: int,
    scanner_exit: int | None,
    openjml_exit: int | None,
    prompt_path: Path | None,
    stdout_jsonl: Path | None,
    stderr_log: Path | None,
    last_message_path: Path | None,
    verified_java: Path,
    usage: dict[str, int] | None,
) -> None:
    lines = [
        "# Verify Metrics",
        "",
        "- Stage: `verify`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Attempts: `{attempts}`",
        f"- Last Codex exit code: `{last_codex_exit}`",
        f"- Anti-cheating scanner exit code: `{scanner_exit if scanner_exit is not None else 'not_run'}`",
        f"- OpenJML exit code: `{openjml_exit if openjml_exit is not None else 'not_run'}`",
        f"- Verified Java: `{verified_java}`",
    ]
    if prompt_path:
        lines.append(f"- Prompt file: `{prompt_path}`")
    if stdout_jsonl:
        lines.append(f"- Codex stdout JSONL: `{stdout_jsonl}`")
    if stderr_log:
        lines.append(f"- Codex stderr log: `{stderr_log}`")
    if last_message_path:
        lines.append(f"- Codex last message: `{last_message_path}`")
    if usage:
        for key in ("input_tokens", "cached_input_tokens", "output_tokens"):
            if key in usage:
                lines.append(f"- Codex CLI {key}: `{usage[key]}`")
    elif prompt_path:
        lines.append(f"- Approx prompt tokens: `{token_count(prompt_path)}`")
        if last_message_path:
            lines.append(f"- Approx last-message tokens: `{token_count(last_message_path)}`")
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex for Java/OpenJML verification.")
    parser.add_argument("input_java", help="Path to input Java file.")
    parser.add_argument("--class-name", help="Java class name. Defaults to PascalCase filename stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to verify skill.")
    parser.add_argument("--workspace-name", help="Workspace/output stem. Defaults to input filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--codex-bin", default="codex")
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--max-attempts", type=int, default=1)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--export-examples",
        action="store_true",
        help="If verify succeeds, export the workspace into experiences/end-end/<name>/ unless that example already exists.",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    input_java = Path(args.input_java)
    if not input_java.is_absolute():
        input_java = (REPO_ROOT / input_java).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not input_java.exists():
        print(f"input Java not found: {input_java}", file=sys.stderr)
        return 2
    if input_java.suffix != ".java":
        print(f"input file must be .java: {input_java}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    stem = args.workspace_name or input_java.stem
    timestamp = args.timestamp or timestamp_now()
    class_name = args.class_name or class_name_from_stem(stem)
    workspace = OUTPUT_ROOT / f"verify_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    original_dir = workspace / "original"
    verified_dir = workspace / "verified"
    logs_dir.mkdir(parents=True, exist_ok=True)
    original_dir.mkdir(parents=True, exist_ok=True)
    verified_dir.mkdir(parents=True, exist_ok=True)
    original_java = original_dir / input_java.name
    verified_java = verified_dir / input_java.name
    shutil.copy2(input_java, original_java)
    shutil.copy2(input_java, verified_java)
    write_fingerprint(workspace, input_java, original_java, verified_java, class_name)

    emit(f"workspace={workspace}")
    emit(f"verified_java={verified_java}")

    start = time.time()
    start_iso = iso_now()
    attempts = 0
    last_codex_exit = 0
    scanner_exit: int | None = None
    openjml_exit: int | None = None
    last_prompt: Path | None = None
    last_stdout: Path | None = None
    last_stderr: Path | None = None
    last_message: Path | None = None
    last_usage: dict[str, int] | None = None

    if args.dry_run:
        run_label = timestamp_now()
        last_prompt = logs_dir / f"codex_prompt_{run_label}.txt"
        last_stdout = logs_dir / f"codex_stdout_{run_label}.jsonl"
        last_stderr = logs_dir / f"codex_stderr_{run_label}.log"
        last_message = logs_dir / f"codex_last_message_{run_label}.txt"
        last_prompt.write_text(build_prompt(skill_path, original_java, verified_java, workspace, class_name, 1), encoding="utf-8")
        last_stdout.write_text("", encoding="utf-8")
        last_stderr.write_text("", encoding="utf-8")
        last_message.write_text("Dry run: Codex was not invoked.\n", encoding="utf-8")
        (logs_dir / "annotation_reasoning.md").write_text("# Annotation Reasoning\n\nDry run only.\n", encoding="utf-8")
        (logs_dir / "issues.md").write_text("# Verify Issues\n\nDry run only.\n", encoding="utf-8")
        status = "Success"
    else:
        codex_env = build_codex_env(logs_dir)
        supports_effort = codex_supports_reasoning_effort(args.codex_bin, codex_env)
        budget_start = time.time()
        status = "Fail"
        for attempt in range(1, max(1, args.max_attempts) + 1):
            attempts = attempt
            remaining = args.timeout_seconds - int(time.time() - budget_start)
            if remaining <= 0:
                last_codex_exit = 124
                append_issue(logs_dir, "Timeout", "Codex verify budget was exhausted before another attempt could start.")
                break
            run_label = timestamp_now()
            last_prompt = logs_dir / f"codex_prompt_{run_label}.txt"
            last_stdout = logs_dir / f"codex_stdout_{run_label}.jsonl"
            last_stderr = logs_dir / f"codex_stderr_{run_label}.log"
            last_message = logs_dir / f"codex_last_message_{run_label}.txt"
            last_prompt.write_text(
                build_prompt(skill_path, original_java, verified_java, workspace, class_name, attempt),
                encoding="utf-8",
            )
            cmd = [
                args.codex_bin,
                "--dangerously-bypass-approvals-and-sandbox",
                "exec",
                "--json",
                "--skip-git-repo-check",
                "-C",
                str(REPO_ROOT),
                "-o",
                str(last_message),
            ]
            if args.model:
                cmd.extend(["--model", args.model])
            if args.reasoning_effort and supports_effort:
                cmd.extend(["--reasoning-effort", args.reasoning_effort])
            cmd.append("-")
            try:
                with last_stdout.open("w", encoding="utf-8") as out_f, last_stderr.open("w", encoding="utf-8") as err_f:
                    proc = subprocess.run(
                        cmd,
                        input=last_prompt.read_text(encoding="utf-8"),
                        text=True,
                        stdout=out_f,
                        stderr=err_f,
                        cwd=REPO_ROOT,
                        env=codex_env,
                        timeout=remaining,
                    )
                last_codex_exit = proc.returncode
            except subprocess.TimeoutExpired:
                last_codex_exit = 124
                last_stderr.write_text("Codex execution timed out.\n", encoding="utf-8")
            filter_stderr(last_stderr)
            last_usage = parse_usage(last_stdout)

            fingerprint_ok, fingerprint_detail = validate_fingerprint(workspace)
            if not fingerprint_ok:
                append_issue(
                    logs_dir,
                    "Fingerprint validation failed",
                    (
                        f"{fingerprint_detail}. Read `experiences/INDEX.md` and fill "
                        "`logs/workspace_fingerprint.json` with non-empty semantic_description "
                        "and controlled keywords."
                    ),
                )
                continue

            scanner_exit = run_scanner(original_java, verified_java, logs_dir, run_label)
            if scanner_exit != 0:
                append_issue(logs_dir, "Anti-cheating scan failed", f"See `cheating_scan_stderr_{run_label}.log`.")
                continue
            openjml_exit = run_openjml(verified_java, logs_dir, run_label)
            if openjml_exit != 0:
                append_issue(logs_dir, "OpenJML failed", f"See `openjml_stderr_{run_label}.log` and `openjml_stdout_{run_label}.log`.")
                continue
            status = "Success"
            break
        if not (logs_dir / "annotation_reasoning.md").exists():
            (logs_dir / "annotation_reasoning.md").write_text(
                "# Annotation Reasoning\n\nNo annotation reasoning log was produced.\n",
                encoding="utf-8",
            )
        if not (logs_dir / "issues.md").exists():
            (logs_dir / "issues.md").write_text("# Verify Issues\n\nNo issues recorded.\n", encoding="utf-8")

    end_iso = iso_now()
    write_metrics(
        logs_dir / "metrics.md",
        status=status,
        dry_run=args.dry_run,
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - start,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        attempts=attempts,
        last_codex_exit=last_codex_exit,
        scanner_exit=scanner_exit,
        openjml_exit=openjml_exit,
        prompt_path=last_prompt,
        stdout_jsonl=last_stdout,
        stderr_log=last_stderr,
        last_message_path=last_message,
        verified_java=verified_java,
        usage=last_usage,
    )
    if status == "Success" and args.export_examples:
        exported, export_detail = export_experience_if_needed(workspace)
        if exported:
            emit(f"experience={export_detail}")
        else:
            emit(f"experience_export={export_detail}")
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
