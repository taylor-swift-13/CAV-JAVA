#!/usr/bin/env python3
"""Audit-stage deterministic scan for a QCP verify result.

Wraps the conservative scanner in ``check_qcp_cheating.py`` and emits the unified
``findings.json`` the audit stage feeds to the agent. ``run_audit.py`` invokes
this as a subprocess (mirroring how the Java pipeline's ``run_audit.py`` invokes
``audit_jml.py``); the agent then reads ``findings.json`` and renders the verdict.

Categories come from ``check_qcp_cheating`` (proof_stub in proof_manual,
manual_axiom, forbidden_import, contract_weakening). Compile-replay is left to
the agent per ``experiences/general/COMPILE.md``; this script does not run coqc.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_qcp_cheating


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Emit findings.json for the audit stage.")
    p.add_argument("--original", help="Original contract C file.")
    p.add_argument("--verified", help="Verified (annotated) C file.")
    p.add_argument("--proof", action="append", default=[], help="A generated proof .v (repeatable).")
    p.add_argument("--function-name", default="")
    p.add_argument("--findings", required=True, help="Output findings.json path.")
    return p


def main() -> int:
    args = build_parser().parse_args()
    original_c = Path(args.original) if args.original else None
    verified_c = Path(args.verified) if args.verified else None
    proof_files = [Path(p) for p in args.proof]

    findings = check_qcp_cheating.scan_paths(
        original_c=original_c, verified_c=verified_c, proof_files=proof_files)
    summary = check_qcp_cheating.summarize(findings)
    doc = {
        "function_name": args.function_name,
        "findings": findings,
        "summary": summary,
        "scanned": {
            "original_c": bool(original_c and original_c.exists()),
            "verified_c": bool(verified_c and verified_c.exists()),
            "proof_files": sorted(p.name for p in proof_files if p.exists()),
        },
    }
    out = Path(args.findings)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"deterministic scan: {summary}")
    for f in findings:
        print(f"[{f['severity']}] {f['category']} {f['file']}:{f['line']} | {f['snippet']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
