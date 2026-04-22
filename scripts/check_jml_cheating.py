#!/usr/bin/env python3
"""Scan Java/JML files for verification bypasses.

This is intentionally conservative. A false positive should be resolved by
rewriting the proof aid into a checked OpenJML artifact or by documenting and
adjusting the scanner deliberately.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys


FORBIDDEN_PATTERNS: list[tuple[str, re.Pattern[str], str]] = [
    ("jml_assume", re.compile(r"//@\s*assume\b|/\*@[^*]*\bassume\b", re.IGNORECASE), "JML assume is not allowed"),
    ("jml_axiom", re.compile(r"\baxiom\b", re.IGNORECASE), "Unchecked axioms are not allowed"),
    ("admitted", re.compile(r"\bAdmitted\b", re.IGNORECASE), "Admitted proofs are not allowed"),
    ("skipesc", re.compile(r"\bskipesc\b", re.IGNORECASE), "OpenJML ESC suppression is not allowed"),
    ("nowarn", re.compile(r"\bnowarn\b", re.IGNORECASE), "Warning suppression is not allowed"),
    ("native_method", re.compile(r"\bnative\b"), "Native methods can hide behavior from verification"),
    ("reflection", re.compile(r"\bClass\s*<|\bClass\.forName\b|\bjava\.lang\.reflect\b"), "Reflection is not allowed in verified examples"),
    ("runtime_exit", re.compile(r"\bSystem\.exit\s*\("), "System.exit is not allowed in verified examples"),
]

CONTRACT_KEYWORDS = ("requires", "ensures", "assignable")


@dataclass
class Finding:
    path: Path
    line_no: int
    code: str
    message: str
    line: str


def iter_findings(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    for line_no, line in enumerate(text.splitlines(), start=1):
        for code, pattern, message in FORBIDDEN_PATTERNS:
            if pattern.search(line):
                findings.append(Finding(path, line_no, code, message, line.strip()))
    return findings


def normalize_contract_line(line: str) -> str:
    if "//@" in line:
        line = line.split("//@", 1)[1]
    elif "/*@" in line:
        line = line.split("/*@", 1)[1]
    line = line.strip()
    line = re.sub(r"^//@\s*", "", line)
    line = re.sub(r"^/\*@\s*", "", line)
    line = re.sub(r"\*/$", "", line)
    line = re.sub(r"\s+", " ", line)
    return line.strip()


def contract_lines(path: Path) -> list[str]:
    result: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        normalized = normalize_contract_line(line)
        lowered = normalized.lower()
        if any(lowered.startswith(keyword) for keyword in CONTRACT_KEYWORDS):
            result.append(normalized)
    return result


def baseline_findings(baseline: Path, candidate: Path) -> list[str]:
    missing: list[str] = []
    candidate_lines = set(contract_lines(candidate))
    for line in contract_lines(baseline):
        if line not in candidate_lines:
            missing.append(line)
    return missing


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Scan Java/JML files for verification bypasses.")
    parser.add_argument("java_file", help="Java file to scan.")
    parser.add_argument("--baseline", help="Original Java file whose contract clauses must be preserved.")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    java_file = Path(args.java_file).resolve()
    if not java_file.exists():
        print(f"file not found: {java_file}", file=sys.stderr)
        return 2
    if java_file.suffix != ".java":
        print(f"expected .java file: {java_file}", file=sys.stderr)
        return 2

    failed = False
    for finding in iter_findings(java_file):
        failed = True
        print(
            f"{finding.path}:{finding.line_no}: {finding.code}: {finding.message}: {finding.line}",
            file=sys.stderr,
        )

    if args.baseline:
        baseline = Path(args.baseline).resolve()
        if not baseline.exists():
            print(f"baseline not found: {baseline}", file=sys.stderr)
            return 2
        missing = baseline_findings(baseline, java_file)
        for line in missing:
            failed = True
            print(
                f"{java_file}: contract_weakening: missing baseline clause: {line}",
                file=sys.stderr,
            )

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
