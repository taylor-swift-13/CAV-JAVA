#!/usr/bin/env python3
"""Closed-loop multi-agent orchestrator for the C/QCP flow.

Two critic-gated blocks plus an experience pass:

  * Contract block: ``run_contract`` -> ``run_eval``. If the eval critic does not
    return ``Spec verdict: Correct`` and rounds remain, re-run the contract with
    the eval findings injected (``--restart-context-file``).
  * Verify block: ``run_verify`` -> ``run_audit``. If the audit critic does not
    return ``VerifiedClean``/``VerifiedWithWarnings`` and rounds remain, re-run
    verify with the audit findings injected.
  * Consolidate: feed every stage workspace to ``run_consolidate --scope all``.
  * Cost: roll every workspace up with ``agent_metrics.write_pipeline_cost_summary``.

Each block is a hand-rolled budget loop rather than ``agent_loop.run`` because the
orchestrator must carry each critic's findings forward into the *next* solver run
(``agent_loop.run`` only feeds restart context to its first attempt).
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_metrics

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"


def emit(msg: str) -> None:
    print(f"[pipeline] {msg}", flush=True)


def run_stage(cmd: list[str]) -> int:
    """Run a sub-runner, streaming its output. Return its exit code."""
    emit("$ " + " ".join(str(c) for c in cmd))
    proc = subprocess.run(cmd, cwd=REPO_ROOT)
    return proc.returncode


def read_line_value(path: Path, marker: str) -> str | None:
    if not path.exists():
        return None
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if marker in line:
            return line.split(marker, 1)[1].strip()
    return None


def write_findings(dest: Path, *, title: str, sources: list[Path]) -> Path:
    """Concatenate critic outputs into one restart-context file for the solver."""
    parts = [f"# {title}\n"]
    for src in sources:
        if src.exists():
            parts.append(f"\n## {src.relative_to(OUTPUT_ROOT) if OUTPUT_ROOT in src.parents else src.name}\n")
            parts.append(src.read_text(encoding="utf-8", errors="replace"))
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text("\n".join(parts) + "\n", encoding="utf-8")
    return dest


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Closed-loop contract↔eval / verify↔audit orchestrator.")
    p.add_argument("target", help="raw/<name>.md (full flow) or input/<name>.c (skip contract).")
    p.add_argument("--function-name")
    p.add_argument("--contract-rounds", type=int, default=2)
    p.add_argument("--verify-rounds", type=int, default=2)
    p.add_argument("--contract-timeout", type=int, default=300)
    p.add_argument("--eval-timeout", type=int, default=900)
    p.add_argument("--verify-timeout", type=int, default=3600)
    p.add_argument("--audit-timeout", type=int, default=900)
    p.add_argument("--consolidate-timeout", type=int, default=600)
    p.add_argument("--skip-eval", action="store_true", help="Run contract without the eval gate.")
    p.add_argument("--skip-audit", action="store_true", help="Run verify without the audit gate.")
    p.add_argument("--no-consolidate", action="store_true")
    p.add_argument("--force", action="store_true", help="Continue to verify even if eval never reaches Correct.")
    p.add_argument("--config", default=None)
    p.add_argument("--agent", choices=["codex", "claude"], default=None)
    p.add_argument("--model", default=None)
    p.add_argument("--dry-run", action="store_true")
    return p


def common_flags(args) -> list[str]:
    flags: list[str] = []
    if args.config:
        flags += ["--config", args.config]
    if args.agent:
        flags += ["--agent", args.agent]
    if args.model:
        flags += ["--model", args.model]
    if args.dry_run:
        flags += ["--dry-run"]
    return flags


def main() -> int:
    args = build_parser().parse_args()
    target = Path(args.target)
    if not target.is_absolute():
        target = (REPO_ROOT / target).resolve()
    if not target.exists():
        print(f"target not found: {target}", file=sys.stderr)
        return 2
    name = args.function_name or target.stem
    is_raw = target.suffix == ".md"
    base_ts = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    pipeline_dir = OUTPUT_ROOT / f"pipeline_{base_ts}_{name}"
    pipeline_dir.mkdir(parents=True, exist_ok=True)
    workspaces: list[Path] = []
    cf = common_flags(args)
    input_c = INPUT_ROOT / f"{name}.c"

    emit(f"target={target} name={name} raw={is_raw} dir={pipeline_dir}")

    # ---- Contract block (contract -> eval) ----
    eval_verdict = None
    if is_raw:
        restart_file = None
        for rnd in range(1, args.contract_rounds + 1):
            ts = f"{base_ts}c{rnd}"
            contract_ws = OUTPUT_ROOT / f"contract_{ts}_{name}"
            cmd = [sys.executable, str(SCRIPTS / "run_contract.py"), str(target),
                   "--function-name", name, "--timestamp", ts, "--workspace-name", name,
                   "--timeout-seconds", str(args.contract_timeout), *cf]
            if restart_file:
                cmd += ["--restart-context-file", str(restart_file)]
            if run_stage(cmd) != 0:
                emit(f"contract round {rnd} returned nonzero")
            workspaces.append(contract_ws)

            if args.skip_eval:
                eval_verdict = "Correct"  # gate bypassed
                break

            ets = f"{base_ts}e{rnd}"
            eval_ws = OUTPUT_ROOT / f"eval_{ets}_{name}"
            ecmd = [sys.executable, str(SCRIPTS / "run_eval.py"), str(input_c),
                    "--function-name", name, "--timestamp", ets, "--workspace-name", name,
                    "--timeout-seconds", str(args.eval_timeout), *cf]
            run_stage(ecmd)
            workspaces.append(eval_ws)
            eval_verdict = read_line_value(eval_ws / "logs" / "final_result.md", "Spec verdict:")
            emit(f"contract round {rnd}: eval verdict={eval_verdict}")
            if args.dry_run:
                break  # wiring exercised; no real verdict to gate on
            if eval_verdict == "Correct":
                break
            if rnd < args.contract_rounds:
                restart_file = write_findings(
                    pipeline_dir / f"eval_findings_r{rnd}.md", title=f"Eval findings (round {rnd})",
                    sources=[eval_ws / "logs" / "final_result.md", eval_ws / "evaluation" / "evaluation.json"])

        if not args.skip_eval and not args.dry_run and eval_verdict != "Correct" and not args.force:
            emit(f"contract gate not met (eval verdict={eval_verdict}); stopping before verify (use --force to continue)")
            _finish(workspaces, pipeline_dir, args, name, status="contract_gate_failed")
            return 1
    else:
        input_c = target

    # ---- Verify block (verify -> audit) ----
    audit_verdict = None
    restart_file = None
    for rnd in range(1, args.verify_rounds + 1):
        ts = f"{base_ts}v{rnd}"
        verify_ws = OUTPUT_ROOT / f"verify_{ts}_{name}"
        cmd = [sys.executable, str(SCRIPTS / "run_verify.py"), str(input_c),
               "--function-name", name, "--timestamp", ts, "--workspace-name", name,
               "--timeout-seconds", str(args.verify_timeout), *cf]
        if restart_file:
            cmd += ["--restart-context-file", str(restart_file)]
        if run_stage(cmd) != 0:
            emit(f"verify round {rnd} returned nonzero")
        workspaces.append(verify_ws)

        if args.skip_audit:
            audit_verdict = "VerifiedClean"  # gate bypassed
            break

        ats = f"{base_ts}a{rnd}"
        audit_ws = OUTPUT_ROOT / f"audit_{ats}_{name}"
        acmd = [sys.executable, str(SCRIPTS / "run_audit.py"), str(verify_ws),
                "--function-name", name, "--timestamp", ats, "--workspace-name", name,
                "--timeout-seconds", str(args.audit_timeout), *cf]
        run_stage(acmd)
        workspaces.append(audit_ws)
        audit_verdict = read_line_value(audit_ws / "logs" / "final_result.md", "Audit verdict:")
        emit(f"verify round {rnd}: audit verdict={audit_verdict}")
        if args.dry_run:
            audit_verdict = "VerifiedClean"  # wiring exercised; no real verdict to gate on
            break
        if audit_verdict in ("VerifiedClean", "VerifiedWithWarnings"):
            break
        if rnd < args.verify_rounds:
            restart_file = write_findings(
                pipeline_dir / f"audit_findings_r{rnd}.md", title=f"Audit findings (round {rnd})",
                sources=[audit_ws / "logs" / "final_result.md", audit_ws / "audit" / "findings.json"])

    status = "success" if audit_verdict in ("VerifiedClean", "VerifiedWithWarnings") else "audit_gate_failed"
    _finish(workspaces, pipeline_dir, args, name, status=status)
    return 0 if status == "success" else 1


def _finish(workspaces, pipeline_dir, args, name, *, status) -> None:
    # ---- Consolidate ----
    if not args.no_consolidate and not args.dry_run:
        ccmd = [sys.executable, str(SCRIPTS / "run_consolidate.py"), *[str(w) for w in workspaces],
                "--scope", "all", "--timeout-seconds", str(args.consolidate_timeout)]
        if args.config:
            ccmd += ["--config", args.config]
        if args.agent:
            ccmd += ["--agent", args.agent]
        run_stage(ccmd)

    # ---- Cost summary ----
    cost = pipeline_dir / "cost_summary.md"
    try:
        agent_metrics.write_pipeline_cost_summary(workspaces, cost)
        emit(f"cost_summary={cost}")
    except Exception as exc:  # noqa: BLE001 - cost rollup is best-effort
        emit(f"cost_summary_failed: {exc}")

    summary = {"status": status, "name": name,
               "workspaces": [str(w) for w in workspaces]}
    (pipeline_dir / "pipeline_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    emit(f"status={status} workspaces={len(workspaces)} summary={pipeline_dir / 'pipeline_summary.json'}")


if __name__ == "__main__":
    sys.exit(main())
