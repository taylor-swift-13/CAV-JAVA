#!/usr/bin/env python3
"""Deterministic QCP ``coqc`` invocation.

Compiles a single ``.v`` under the QualifiedCProgramming load-path so callers can
run Coq's own reduction machinery on closed terms. The load-path mirrors the
stable compile template in ``experiences/general/COMPILE/README.md`` §5: coqc runs with
``QualifiedCProgramming/SeparationLogic`` as its working directory and the base
``-R`` set below resolves every QCP library a generated ``.v`` may ``Require``.

Primary use: ``run_eval`` discharges *computable* ``needs_judge`` clauses by
generating a tiny ``.v`` with ``Eval vm_compute in <closed_term>.`` and reading
the reduced normal form off stdout — Coq reduction of a closed term, not C
execution and not a proof. The same helper can later back audit's compile
replay cross-check.
"""
from __future__ import annotations

import os
from pathlib import Path
import subprocess


# This module lives at <repo>/scripts/, so the repo root is one level up.
REPO_ROOT = Path(__file__).resolve().parents[1]
QCP_SL_DIR = REPO_ROOT / "QualifiedCProgramming" / "SeparationLogic"

# Base load-path, relative to QCP_SL_DIR. Keep in sync with experiences/general/COMPILE/README.md §5.
BASE_LOAD_PATH: list[tuple[str, str]] = [
    ("SeparationLogic", "SimpleC.SL"),
    ("unifysl", "Logic"),
    ("sets", "SetsClass"),
    ("compcert_lib", "compcert.lib"),
    ("auxlibs", "AUXLib"),
    ("examples", "SimpleC.EE"),
    ("StrategyLib", "SimpleC.StrategyLib"),
    ("Common", "SimpleC.Common"),
    ("fixedpoints", "FP"),
    ("MonadLib", "MonadLib"),
    ("listlib", "ListLib"),
]


# Coq compile intermediates. `.aux` covers both `name.aux` and the hidden
# `.name.aux` Coq emits (its suffix is still `.aux`).
COMPILE_ARTIFACT_SUFFIXES: tuple[str, ...] = (".vo", ".vok", ".vos", ".glob", ".aux")


def coqc_bin() -> str:
    """coqc binary; override with ``$COQC`` (e.g. an absolute opam path)."""
    return os.environ.get("COQC", "coqc")


def clean_compile_artifacts(directory: Path, *, recursive: bool = True) -> list[str]:
    """Delete Coq compile intermediates under ``directory``; keep ``.v``/``.c``.

    Use only on workspace dirs (``coq/generated``, ``evaluation/compute``, an
    audit ``verified/`` copy) — never on the shared QCP tree, whose prebuilt
    ``examples/*.vo`` must survive. Returns the paths removed.
    """
    d = Path(directory)
    if not d.exists():
        return []
    removed: list[str] = []
    for p in (d.rglob("*") if recursive else d.iterdir()):
        if p.is_file() and p.suffix in COMPILE_ARTIFACT_SUFFIXES:
            try:
                p.unlink()
                removed.append(str(p))
            except OSError:
                pass
    return removed


def _base_args() -> list[str]:
    args: list[str] = []
    for path, prefix in BASE_LOAD_PATH:
        args += ["-R", path, prefix]
    return args


def build_command(
    v_file: Path,
    *,
    extra_r: list[tuple[str, str]] | None = None,
    extra_q: list[tuple[str, str]] | None = None,
    coqc: str | None = None,
) -> list[str]:
    """Assemble the coqc argv for ``v_file`` (resolved absolute).

    ``extra_q`` are added as ``-Q`` (e.g. a problem's ``original/`` dir with the
    empty prefix); ``extra_r`` as ``-R`` (e.g. a workspace ``generated/`` dir
    with its ``SimpleC.EE.CAV.*`` prefix). Both come before the file, after BASE.
    """
    cmd = [coqc or coqc_bin(), *_base_args()]
    for path, prefix in (extra_q or []):
        cmd += ["-Q", str(path), prefix]
    for path, prefix in (extra_r or []):
        cmd += ["-R", str(path), prefix]
    cmd.append(str(Path(v_file).resolve()))
    return cmd


def run_coqc(
    v_file: Path,
    *,
    extra_r: list[tuple[str, str]] | None = None,
    extra_q: list[tuple[str, str]] | None = None,
    coqc: str | None = None,
    env: dict[str, str] | None = None,
    timeout_seconds: int = 300,
) -> tuple[int, str, str]:
    """Compile ``v_file`` under the QCP load-path. Return ``(rc, stdout, stderr)``.

    cwd is ``QualifiedCProgramming/SeparationLogic`` so the relative BASE ``-R``
    paths resolve. On timeout returns ``(124, "", <message>)``.
    """
    cmd = build_command(v_file, extra_r=extra_r, extra_q=extra_q, coqc=coqc)
    try:
        proc = subprocess.run(
            cmd,
            cwd=QCP_SL_DIR,
            env=env or os.environ.copy(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return 124, "", f"coqc timed out after {timeout_seconds}s"
    except OSError as exc:
        return 127, "", f"coqc not runnable: {exc}"
    return proc.returncode, proc.stdout, proc.stderr


def parse_eval_normal_form(stdout: str) -> str | None:
    """Extract the reduced term printed by ``Eval vm_compute in ...``.

    Coq prints ``     = <value>`` then ``     : <type>``. Returns ``<value>``
    (possibly multi-line, joined) for the last such block, or None.
    """
    lines = stdout.splitlines()
    value_lines: list[str] | None = None
    collecting: list[str] | None = None
    for raw in lines:
        stripped = raw.strip()
        if stripped.startswith("="):
            collecting = [stripped[1:].strip()]
        elif collecting is not None and stripped.startswith(":"):
            value_lines = collecting
            collecting = None
        elif collecting is not None:
            collecting.append(stripped)
    if value_lines is None and collecting:
        value_lines = collecting
    if value_lines is None:
        return None
    return " ".join(p for p in value_lines if p).strip() or None
