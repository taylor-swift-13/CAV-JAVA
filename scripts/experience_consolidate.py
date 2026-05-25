#!/usr/bin/env python3
"""Final experience-consolidation unit for the C/QCP flow."""
from __future__ import annotations

from dataclasses import dataclass, field
import datetime as dt
import hashlib
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_loop


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERAL_DIR = REPO_ROOT / "experiences" / "general"

SCOPE_FILES: dict[str, list[str]] = {
    "contract": ["CONTRACT.md", "EVAL.md", "AUDIT.md"],
    "verify": ["SYMEXEC.md", "ASSERTION.md", "INV.md", "PROOF.md", "COMPILE.md", "AUDIT.md"],
    "all": ["CONTRACT.md", "EVAL.md", "SYMEXEC.md", "ASSERTION.md", "INV.md", "PROOF.md", "COMPILE.md", "AUDIT.md"],
}


@dataclass
class ConsolidateResult:
    changed: list[str] = field(default_factory=list)
    ran: bool = False
    detail: str = "skipped"


def snapshot() -> dict[str, str]:
    snap: dict[str, str] = {}
    if not GENERAL_DIR.exists():
        return snap
    for path in sorted(GENERAL_DIR.rglob("*")):
        if path.is_file():
            snap[path.relative_to(GENERAL_DIR).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return snap


def changed_files(before: dict[str, str]) -> list[str]:
    after = snapshot()
    return sorted(name for name, digest in after.items() if before.get(name) != digest)


def _build_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".consolidate_cache",
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


def build_prompt(scope: str, workspaces: list[Path]) -> str:
    files = SCOPE_FILES.get(scope, SCOPE_FILES["all"])
    file_list = ", ".join(f"`experiences/general/{f}`" for f in files)
    ws_list = "\n".join(f"  - `{w}`" for w in workspaces) or "  - (none)"
    return f"""You are the final experience-consolidation agent for a C/QCP `{scope}` flow.

Read the logs of the workspaces this flow produced:
{ws_list}

In each workspace, inspect at least:
- `logs/metrics.md`
- `logs/issues.md`
- `logs/final_result.md`
- reasoning logs such as `reasoning.md`, `annotation_reasoning.md`,
  `proof_reasoning.md`, `test_reasoning.md`, `continue.md`
- compile or replay logs
- audit findings when present

Then decide whether this run taught any GENERAL, reusable lesson, and if so
merge it into the relevant file(s) under `experiences/general/` for this scope,
usually {file_list}.

Capture TWO kinds of reusable lesson:
1. Correctness — how to produce a result that actually verifies (e.g. which
   annotations / proof obligations matter, what a valid `proof_auto.v` vs
   `proof_manual.v` looks like, what counts as cheating).
2. Efficiency — analyze what made this run SLOW or wasteful (retries, dead-end
   fixes, re-deriving something that already existed, a critic re-run, time
   spent re-discovering a convention), and record the reusable shortcut that
   would avoid it next time (e.g. "reuse `proof_manual.v` from a prior
   same-SHA256 workspace and only update the module path", "don't try X, it
   never works", "recognize convention Y up front"). File these efficiency
   rules in the same scoped file as the topic they concern.

Hard rules:
- Touch nothing outside `experiences/general/`.
- Only record reusable rules, not task-specific anecdotes.
- If an existing numbered rule should be sharpened, edit it in place instead of
  appending a near-duplicate.
- If this run taught nothing general, leave the experience files unchanged.
- Keep the files in markdown; preserve their existing scope headers.
- Date any new content {dt.date.today().isoformat()}.
"""


def consolidate(
    *,
    scope: str,
    workspaces: list[Path],
    logs_dir: Path,
    agent: str = "codex",
    codex_bin: str = "codex",
    claude_bin: str = "claude",
    model: str = "",
    reasoning_effort: str = "medium",
    timeout_seconds: int = 600,
    dry_run: bool = False,
) -> ConsolidateResult:
    if dry_run:
        return ConsolidateResult(ran=False, detail="dry run; consolidation skipped")

    before = snapshot()
    logs_dir.mkdir(parents=True, exist_ok=True)
    env = _build_env(logs_dir)
    prompt = build_prompt(scope, workspaces)
    (logs_dir / "consolidate_prompt.txt").write_text(prompt, encoding="utf-8")

    exit_code, timed_out = agent_loop.run_agent_round(
        agent=agent,
        codex_bin=codex_bin,
        claude_bin=claude_bin,
        model=model,
        reasoning_effort=reasoning_effort,
        prompt=prompt,
        stdout_jsonl=logs_dir / "consolidate_stdout.jsonl",
        stderr_log=logs_dir / "consolidate_stderr.log",
        last_message_path=logs_dir / "consolidate_last_message.txt",
        env=env,
        timeout_seconds=timeout_seconds,
    )
    changed = changed_files(before)
    note = "timed out" if timed_out else f"exit {exit_code}"
    if changed:
        detail = f"consolidation ({note}) updated " + ", ".join(changed)
    else:
        detail = f"consolidation ({note}) found no general lesson; left experiences/general unchanged"
    return ConsolidateResult(changed=changed, ran=True, detail=detail)
