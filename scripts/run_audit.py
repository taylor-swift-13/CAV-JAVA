#!/usr/bin/env python3
"""Audit-stage runner: the critic that decides whether a verify result is
trustworthy (no weakened contract, no proof stubs, no smuggled assumptions).

Mirrors the other runners. The runner produces the *deterministic* artifacts the
audit SKILL expects — ``audit/findings.json`` from ``audit_scan`` plus the
cheating-scan logs — then the agent reads them, inspects the copied files, and
renders one verdict in ``logs/final_result.md``. Compile replay is delegated to
the agent (see ``experiences/general/COMPILE.md``); the runner does not run coqc.

Gate: ``logs/metrics.md`` ends in ``Final Result: Success`` and
``logs/final_result.md`` carries ``Audit verdict: VerifiedClean`` or
``VerifiedWithWarnings``.
"""
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics

REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

DEFAULT_SKILL = REPO_ROOT / "skills" / "audit" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
ANNOTATED_ROOT = REPO_ROOT / "annotated"
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


def emit_log(message: str) -> None:
    print(f"[audit] {message}", flush=True)


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".codex_cache", "XDG_STATE_HOME": ".state",
        "XDG_DATA_HOME": ".data", "XDG_CONFIG_HOME": ".config",
        "TMPDIR": ".tmp", "TMP": ".tmp", "TEMP": ".tmp",
    }.items():
        path = logs_dir / dirname
        path.mkdir(parents=True, exist_ok=True)
        env[name] = str(path)
    return env


def codex_supports_reasoning_effort(codex_bin: str, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, cwd=REPO_ROOT, env=env, timeout=10)
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    kept = [ln for ln in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines()
            if not any(p in ln for p in NOISE_PATTERNS)]
    stderr_log.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


def final_result_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "final_result.md"


def resolve_verify_artifacts(verify_ws: Path, function_name: str | None
                             ) -> tuple[Path | None, Path | None, list[Path]]:
    """From a verify workspace, locate (original_c, verified_c, proof_files)."""
    original_dir = verify_ws / "original"
    originals = sorted(original_dir.glob("*.c"))
    original_c = None
    if function_name:
        cand = original_dir / f"{function_name}.c"
        original_c = cand if cand.exists() else (originals[0] if originals else None)
    else:
        original_c = originals[0] if originals else None
    verified_c = ANNOTATED_ROOT / f"{verify_ws.name}.c"
    if not verified_c.exists():
        verified_c = None
    proof_files = sorted((verify_ws / "coq" / "generated").glob("*_proof_*.v"))
    return original_c, verified_c, proof_files


def bootstrap_workspace(workspace_path: Path, original_c: Path | None,
                        verified_c: Path | None, proof_files: list[Path]) -> dict:
    for sub in ("logs", "original", "verified", "audit"):
        (workspace_path / sub).mkdir(parents=True, exist_ok=True)
    copied = {"original_c": None, "verified_c": None, "proofs": []}
    if original_c and original_c.exists():
        dst = workspace_path / "original" / original_c.name
        shutil.copy2(original_c, dst)
        copied["original_c"] = dst
    if verified_c and verified_c.exists():
        dst = workspace_path / "verified" / verified_c.name
        shutil.copy2(verified_c, dst)
        copied["verified_c"] = dst
    for pf in proof_files:
        dst = workspace_path / "verified" / pf.name
        shutil.copy2(pf, dst)
        copied["proofs"].append(dst)
    return copied


def run_deterministic_scan(workspace_path: Path, copied: dict, function_name: str) -> dict:
    """Invoke audit_qcp.py to write audit/findings.json + scan logs; return the doc."""
    findings_out = workspace_path / "audit" / "findings.json"
    findings_out.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(REPO_ROOT / "scripts" / "audit_qcp.py"),
           "--findings", str(findings_out), "--function-name", function_name]
    if copied["original_c"]:
        cmd += ["--original", str(copied["original_c"])]
    if copied["verified_c"]:
        cmd += ["--verified", str(copied["verified_c"])]
    for p in copied["proofs"]:
        if p.name.endswith("_proof_manual.v") or p.name.endswith("_proof_auto.v"):
            cmd += ["--proof", str(p)]
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, cwd=REPO_ROOT)
    logs = workspace_path / "logs"
    (logs / "cheating_scan_stdout.log").write_text(proc.stdout, encoding="utf-8")
    (logs / "cheating_scan_stderr.log").write_text(proc.stderr, encoding="utf-8")
    try:
        return json.loads(findings_out.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"function_name": function_name, "findings": [],
                "summary": {"total": 0, "errors": 0, "warnings": 0,
                            "categories": [], "deterministic_clean": True},
                "scanned": {}}


def build_prompt(*, skill_path: Path, workspace_path: Path, function_name: str,
                 findings_doc: dict) -> str:
    return f"""Use this skill as the complete workflow:
{skill_path}

Inputs:
- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Original C: `{workspace_path / 'original'}`
- Verified files (annotated C + generated proofs): `{workspace_path / 'verified'}`
- Deterministic findings (runner-produced): `{workspace_path / 'audit' / 'findings.json'}`
  summary: {json.dumps(findings_doc['summary'], ensure_ascii=False)}

The deterministic cheating scan has already run. Read `findings.json`, inspect
the copied files, and for each finding decide whether it is a real violation or
a justified false positive. Perform the compile-replay cross-check yourself per
`experiences/general/COMPILE.md` and record it in your reasoning. Then write
`audit/findings.md`, `logs/reasoning.md`, `logs/final_result.md` (with one
`Audit verdict:` line) and `logs/metrics.md` (ending in `Final Result:`).
"""


def run_agent_once(*, agent, codex_bin, claude_bin, model, reasoning_effort,
                   prompt, logs_dir, run_label, env, timeout_seconds):
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    if agent == "claude":
        cmd = [claude_bin, "--print", "--dangerously-skip-permissions", "--add-dir",
               str(REPO_ROOT), "--output-format", "stream-json", "--verbose"]
        if model:
            cmd.extend(["--model", model])
    else:
        cmd = [codex_bin, "--dangerously-bypass-approvals-and-sandbox", "exec",
               "--json", "--skip-git-repo-check", "-C", str(REPO_ROOT),
               "-o", str(last_message_path)]
        if model:
            cmd.extend(["--model", model])
        if reasoning_effort and codex_supports_reasoning_effort(codex_bin, env):
            cmd.extend(["--reasoning-effort", reasoning_effort])
        cmd.append("-")
    try:
        with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(cmd, input=prompt, text=True, stdout=out_f,
                                  stderr=err_f, cwd=REPO_ROOT, env=env, timeout=timeout_seconds)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        rc = 124
    filter_stderr_in_place(stderr_log)
    if agent == "claude":
        last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
        if last_message is not None:
            last_message_path.write_text(last_message, encoding="utf-8")
        elif stdout_jsonl.exists():
            last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
    usage = agent_metrics.parse_usage(agent, stdout_jsonl)
    return rc, usage


def read_audit_verdict(workspace_path: Path) -> str | None:
    fr = final_result_path(workspace_path)
    if not fr.exists():
        return None
    for line in fr.read_text(encoding="utf-8", errors="replace").splitlines():
        # Accept both `Audit verdict: X` and the markdown `## Audit verdict: X`.
        if "Audit verdict:" in line:
            return line.split("Audit verdict:", 1)[1].strip()
    return None


def gate_success(workspace_path: Path) -> tuple[bool, str]:
    mp = metrics_path(workspace_path)
    if not mp.exists():
        return False, "missing_metrics"
    saw_success = any(ln.strip() == "Final Result: Success"
                      for ln in mp.read_text(encoding="utf-8", errors="replace").splitlines())
    verdict = read_audit_verdict(workspace_path)
    if saw_success and verdict in ("VerifiedClean", "VerifiedWithWarnings"):
        return True, f"verdict:{verdict}"
    return False, f"verdict:{verdict}|final_result_success:{saw_success}"


def write_metrics(path, *, status, exit_code, start_iso, end_iso, wall_seconds,
                  model, reasoning_effort, verdict, det_summary, usage) -> None:
    lines = [
        "# Audit Metrics", "",
        "- Stage: `audit`",
        f"- Status: `{status}`",
        f"- Exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Deterministic scan: `{det_summary}`",
        f"- Audit verdict: `{verdict}`",
    ]
    lines.extend(agent_metrics.usage_lines(usage))
    lines.append(f"Final Result: {status}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Audit a verify workspace for anti-cheating violations.")
    p.add_argument("verify_workspace", nargs="?", help="A verify workspace dir (output/verify_*).")
    p.add_argument("--original", help="Explicit original C (overrides workspace detection).")
    p.add_argument("--verified", help="Explicit verified/annotated C.")
    p.add_argument("--proof", action="append", default=[], help="Explicit proof .v (repeatable).")
    p.add_argument("--function-name")
    p.add_argument("--skill", default=str(DEFAULT_SKILL))
    p.add_argument("--workspace-name")
    p.add_argument("--timestamp")
    p.add_argument("--config", default=None)
    p.add_argument("--agent", choices=["codex", "claude"], default=None)
    p.add_argument("--model", default=None)
    p.add_argument("--reasoning-effort", default=None)
    p.add_argument("--timeout-seconds", type=int, default=900)
    p.add_argument("--dry-run", action="store_true")
    return p


def main() -> int:
    args = build_parser().parse_args()

    # Resolve inputs: explicit pair, or detect from a verify workspace.
    source_verify_ws: Path | None = None
    if args.original or args.verified:
        original_c = Path(args.original).resolve() if args.original else None
        verified_c = Path(args.verified).resolve() if args.verified else None
        proof_files = [Path(p).resolve() for p in args.proof]
        base_name = (verified_c or original_c).stem if (verified_c or original_c) else "audit"
    elif args.verify_workspace:
        verify_ws = Path(args.verify_workspace)
        if not verify_ws.is_absolute():
            verify_ws = (REPO_ROOT / verify_ws).resolve()
        if not verify_ws.exists():
            print(f"verify workspace not found: {verify_ws}", file=sys.stderr)
            return 2
        source_verify_ws = verify_ws
        original_c, verified_c, proof_files = resolve_verify_artifacts(verify_ws, args.function_name)
        base_name = args.function_name or (original_c.stem if original_c else verify_ws.name)
    else:
        print("provide a verify workspace or --original/--verified", file=sys.stderr)
        return 2

    function_name = args.function_name or (original_c.stem if original_c else base_name)
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.default_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = cfg.bin("codex", "codex")
    claude_bin = cfg.bin("claude", "claude")

    stem = args.workspace_name or base_name
    ts = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"audit_{ts}_{stem}"
    copied = bootstrap_workspace(workspace_path, original_c, verified_c, proof_files)
    logs_dir = workspace_path / "logs"
    env = build_codex_env(logs_dir)
    findings_doc = run_deterministic_scan(workspace_path, copied, function_name)
    det_summary = findings_doc["summary"]
    emit_log(f"workspace={workspace_path}")
    emit_log(f"function_name={function_name} agent={agent} model={model}")
    emit_log(f"deterministic_scan={det_summary}")

    if args.dry_run:
        write_metrics(metrics_path(workspace_path), status="Success", exit_code=0,
                      start_iso=iso_now(), end_iso=iso_now(), wall_seconds=0.0, model=model,
                      reasoning_effort=reasoning_effort, verdict=None, det_summary=det_summary, usage=None)
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    prompt = build_prompt(skill_path=skill_path, workspace_path=workspace_path,
                          function_name=function_name, findings_doc=findings_doc)
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    rc, usage = run_agent_once(agent=agent, codex_bin=codex_bin, claude_bin=claude_bin,
                               model=model, reasoning_effort=reasoning_effort, prompt=prompt,
                               logs_dir=logs_dir, run_label=run_label, env=env,
                               timeout_seconds=args.timeout_seconds)

    # The agent may have run compile-replay coqc inside verified/; drop the
    # .vo/.glob/.aux intermediates, keep the .v/.c copies.
    coq_runner.clean_compile_artifacts(workspace_path / "verified")
    # COMPILE.md §5's template compiles in-place in the SOURCE verify workspace,
    # so the replay leaves intermediates there too — clean those as well.
    if source_verify_ws is not None:
        n_src = len(coq_runner.clean_compile_artifacts(source_verify_ws / "coq"))
        emit_log(f"cleaned_source_verify_artifacts count={n_src}")

    ok, detail = gate_success(workspace_path)
    status = "Success" if ok else "Fail"
    verdict = read_audit_verdict(workspace_path)
    write_metrics(metrics_path(workspace_path), status=status, exit_code=rc,
                  start_iso=start_iso, end_iso=iso_now(), wall_seconds=time.time() - start_wall,
                  model=model, reasoning_effort=reasoning_effort, verdict=verdict,
                  det_summary=det_summary, usage=usage)
    emit_log(f"status={status} verdict={verdict} gate={detail}")
    print(str(workspace_path))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
