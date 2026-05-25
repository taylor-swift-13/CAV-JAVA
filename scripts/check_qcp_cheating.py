#!/usr/bin/env python3
"""Conservative deterministic cheating scanner for QCP verify artifacts.

Importable scan library (used by ``audit_qcp.py``) plus a standalone CLI. Pure,
side-effect-free functions flag the suspicious patterns the audit stage surfaces
before the agent adjudicates. The agent reads the findings plus the copied files
and renders the final verdict; this module never edits anything and never
decides the verdict itself.

Categories (matching ``skills/audit/SKILL.md``):

  * ``proof_stub``        — ``Admitted.`` / ``admit`` / ``Abort.`` in
                            ``proof_manual.v`` ONLY. ``proof_auto.v`` is
                            symexec-generated and is ``Admitted.`` by QCP
                            convention (the real proof burden lives in
                            ``proof_manual.v``), so its stubs are NOT flagged.
  * ``manual_axiom``      — hand-written ``Axiom`` / ``Hypothesis``
  * ``forbidden_import``  — ``Require Import`` outside the known QCP/Coq set
  * ``contract_weakening``— the verified file's ``Require``/``Ensure`` differs
                            from the original contract

Severity: proof_stub / manual_axiom / contract_weakening are ``error``;
forbidden_import is ``warning`` (the agent confirms whether it is truly illicit).
"""
from __future__ import annotations

from pathlib import Path
import re


# Logical-path prefixes that legitimately appear in QCP manual proofs.
ALLOWED_IMPORT_PREFIXES: tuple[str, ...] = (
    "Coq.",
    "AUXLib",
    "SimpleC.",
    "compcert.lib",
    "SetsClass",
    "Logic",
    "FP",
    "MonadLib",
    "ListLib",
    "MaxMinLib",
    "GraphLib",
    "Permutation",
)

_BLOCK_RE = re.compile(r"/\*@(.*?)\*/", re.DOTALL)
_WS_RE = re.compile(r"\s+")
# `From X Require Import a b.` and `Require Import a b.`
_IMPORT_RE = re.compile(r"^\s*(?:From\s+(\S+)\s+)?Require\s+(?:Import|Export)\s+(.+?)\.", re.MULTILINE)


def _normalize(text: str) -> str:
    return _WS_RE.sub(" ", text).strip()


def extract_contract_specs(c_text: str) -> list[str]:
    """Normalized ``/*@ ... */`` blocks that carry a contract (have ``Ensure``).

    The function-header contract holds ``Require``/``Ensure``; body ``Inv`` /
    ``Assert`` blocks do not have ``Ensure`` and are excluded — those are the
    annotations a verified file is *allowed* to add.
    """
    specs: list[str] = []
    for body in _BLOCK_RE.findall(c_text):
        if re.search(r"\bEnsure\b", body):
            specs.append(_normalize(body))
    return specs


def scan_contract_weakening(original_c: str, verified_c: str) -> list[dict]:
    """Flag any change to the contract spec between original and verified."""
    orig = extract_contract_specs(original_c)
    ver = extract_contract_specs(verified_c)
    if orig == ver:
        return []
    return [{
        "category": "contract_weakening",
        "severity": "error",
        "file": "verified",
        "line": 0,
        "snippet": (ver[0] if ver else "<no contract block in verified>")[:400],
        "message": (
            "Verified file's contract (With/Require/Ensure) differs from the "
            "original. Annotations may add Inv/Assert/which-implies but must not "
            "alter the contract. original_specs={} verified_specs={}".format(
                len(orig), len(ver))
        ),
    }]


def _scan_lines(text: str, file_label: str, pattern: re.Pattern, category: str,
                severity: str, message: str) -> list[dict]:
    findings: list[dict] = []
    for i, line in enumerate(text.splitlines(), start=1):
        if pattern.search(line):
            findings.append({
                "category": category,
                "severity": severity,
                "file": file_label,
                "line": i,
                "snippet": line.strip()[:400],
                "message": message,
            })
    return findings


# Tactic/command stubs. `admit` and `Abort`/`Admitted` are whole words; the
# trailing period is how Coq terminates them but we match the keyword to be
# robust to spacing.
_PROOF_STUB_RE = re.compile(r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])")
_AXIOM_RE = re.compile(r"^\s*(Axiom|Hypothesis|Parameter|Conjecture)\s", re.MULTILINE)


def scan_proof_file(text: str, file_label: str, *, flag_stubs: bool = True) -> list[dict]:
    """Scan one proof ``.v`` for stubs, axioms, and forbidden imports.

    ``flag_stubs`` should be True only for ``proof_manual.v``: an ``Admitted.``
    there means a real obligation was skipped. In ``proof_auto.v`` the
    ``Admitted.`` stubs are the normal symexec-generated form and are ignored.
    """
    findings: list[dict] = []
    if flag_stubs:
        findings += _scan_lines(
            text, file_label, _PROOF_STUB_RE, "proof_stub", "error",
            "proof_manual.v contains an admit/Admitted/Abort stub; a manual "
            "obligation was not actually discharged.",
        )
    for i, line in enumerate(text.splitlines(), start=1):
        if _AXIOM_RE.match(line):
            findings.append({
                "category": "manual_axiom",
                "severity": "error",
                "file": file_label,
                "line": i,
                "snippet": line.strip()[:400],
                "message": "Hand-written Axiom/Hypothesis/Parameter assumes the "
                           "goal instead of proving it.",
            })
    for m in _IMPORT_RE.finditer(text):
        origin = m.group(1)  # the `From <origin>` part, if any
        names = m.group(2)
        targets = [origin] if origin else names.split()
        for target in targets:
            if not any(target.startswith(p) or target == p.rstrip(".")
                       for p in ALLOWED_IMPORT_PREFIXES):
                line = text[: m.start()].count("\n") + 1
                findings.append({
                    "category": "forbidden_import",
                    "severity": "warning",
                    "file": file_label,
                    "line": line,
                    "snippet": m.group(0).strip()[:400],
                    "message": f"Import `{target}` is outside the known QCP/Coq "
                               "library set; confirm it is not used to smuggle in "
                               "an assumption.",
                })
                break
    return findings


def scan(
    *,
    original_c: str | None,
    verified_c: str,
    proof_files: dict[str, str],
) -> list[dict]:
    """Run every deterministic check. ``proof_files`` maps label -> file text."""
    findings: list[dict] = []
    if original_c is not None:
        findings += scan_contract_weakening(original_c, verified_c)
    for label, text in proof_files.items():
        # Only proof_manual.v carries a real proof burden; proof_auto.v is
        # generated and Admitted by QCP convention.
        findings += scan_proof_file(text, label, flag_stubs="proof_manual" in label)
    return findings


def summarize(findings: list[dict]) -> dict:
    """Counts by severity, plus the deterministic gate hint."""
    errors = [f for f in findings if f.get("severity") == "error"]
    warnings = [f for f in findings if f.get("severity") == "warning"]
    return {
        "total": len(findings),
        "errors": len(errors),
        "warnings": len(warnings),
        "categories": sorted({f.get("category", "?") for f in findings}),
        "deterministic_clean": len(errors) == 0,
    }


def scan_paths(
    *,
    original_c: Path | None,
    verified_c: Path | None,
    proof_files: list[Path],
) -> list[dict]:
    """File-path wrapper around :func:`scan`: read texts, label proof files."""
    orig = original_c.read_text(encoding="utf-8", errors="replace") if original_c and original_c.exists() else None
    ver = verified_c.read_text(encoding="utf-8", errors="replace") if verified_c and verified_c.exists() else ""
    proofs = {p.name: p.read_text(encoding="utf-8", errors="replace") for p in proof_files if p.exists()}
    return scan(original_c=orig, verified_c=ver, proof_files=proofs)


def _build_parser():
    import argparse
    p = argparse.ArgumentParser(description="Conservative cheating scan over QCP verify artifacts.")
    p.add_argument("--original", help="Original contract C file.")
    p.add_argument("--verified", help="Verified (annotated) C file.")
    p.add_argument("--proof", action="append", default=[], help="A generated proof .v (repeatable).")
    return p


def main() -> int:
    import json
    import sys
    args = _build_parser().parse_args()
    findings = scan_paths(
        original_c=Path(args.original) if args.original else None,
        verified_c=Path(args.verified) if args.verified else None,
        proof_files=[Path(p) for p in args.proof],
    )
    json.dump({"findings": findings, "summary": summarize(findings)}, sys.stdout,
              indent=2, ensure_ascii=False)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
