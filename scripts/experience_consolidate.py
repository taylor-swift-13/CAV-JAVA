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
    "contract": ["CONTRACT/README.md", "EVAL/README.md", "AUDIT/README.md"],
    "verify": ["SYMEXEC/README.md", "ASSERTION/README.md", "INV/README.md", "PROOF/README.md", "COMPILE/README.md", "AUDIT/README.md"],
    "all": ["CONTRACT/README.md", "EVAL/README.md", "SYMEXEC/README.md", "ASSERTION/README.md", "INV/README.md", "PROOF/README.md", "COMPILE/README.md", "AUDIT/README.md"],
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

For **efficiency lessons** specifically, also inspect
`logs/agent_stdout_*.jsonl` (the upstream stage agent's harness transcript).
**Do not** read these files sequentially in full — they may be megabytes and
will burn context. Use targeted lookups:
- `grep -c '"type":"tool_use"' logs/agent_stdout_*.jsonl` → total tool calls;
  unusually high counts on a "simple" task indicate flailing.
- Group repeated tool calls (e.g. many similar `grep`s for the same lemma) —
  this is the signature of an agent hunting for something that doesn't exist
  or that it doesn't know how to find.
- Look at the longest stretches between meaningful progress markers
  (`emit_log` lines, file writes, `coqc` invocations) to find dead-ends.
- Compare attempts when `Attempts > 1`: what was the first attempt's
  blocker, and what was the actual fix?

The curated `issues.md` / reasoning logs often miss this self-aware view — the
agent doesn't usually realize it spent 95 calls finding a lemma that doesn't
exist. The jsonl is where that lesson lives. **Note**: this is a special
exemption for the consolidate agent; the standing rule in `skills/COMMON.md`
("don't read your own harness transcript") only forbids reading the *current*
consolidate run's transcript, not the upstream stage's.

Then decide whether this run taught any GENERAL, reusable lesson and where it
belongs in the new folder layout. For this scope the relevant docs are: {file_list}.

Each `experiences/general/<NAME>/` doc has two retrieval surfaces with
**independent numbering**. Universal and topical entries do NOT share a counter.

| Surface | Where it lives | How agents find it |
|---------|----------------|--------------------|
| **Universal** | `<NAME>/README.md` as `## <U>. <title>` sections | The README's 「常见入口」TOC at the top of the file (human-browsed); descriptive titles index by topic |
| **Topical** | `<NAME>/<N>/<slug>.md` + `<NAME>/<N>/<slug>.fingerprint` (one per numbered subfolder) | `scripts/search_fingerprint.py` matches `keywords` + `semantic_description` and returns the `.md` path |

`<U>` (README section counter) and `<N>` (folder counter) are completely
**independent integer sequences**. README's largest § might be 12 while the
folder counter is at 5; that's fine. When you add a universal entry, only
increment `<U>`. When you add a topical entry, only increment `<N>`.

Decide universal vs topical by asking: "does this lesson apply only to a
particular shape of problem (e.g. sll cons, insertion sort, string scan,
binary search), or to every problem in this stage?" If it's clearly
problem-class-specific → topical (numbered subfolder + fingerprint). If
uncertain → default to universal (a section in README.md).

**To add a universal entry**:

1. Open `<NAME>/README.md` and read the existing `## <U>. ...` headings.
2. Append a new `## <max_U + 1>. <Short title> (<date>)` at the bottom.
3. Add a one-line bullet to the「常见入口」TOC at the top of the same file so
   readers can find it by topic.

**To add a topical entry**:

1. `ls experiences/general/<NAME>/` and find the largest existing numeric
   subfolder name (ignore `README.md`). Call it `M`. If none exists, `M = 0`.
2. Create `experiences/general/<NAME>/<M+1>/` (the new folder).
3. Inside, write exactly two sibling files: `<slug>.md` (content) and
   `<slug>.fingerprint` (JSON below). `<slug>` is kebab-case derived from the
   title (e.g. `sll-cons-fold`); the number `<M+1>` is the opaque accumulator
   ID, the slug is the human-readable name.
4. Do NOT add a TOC entry for topical experiences in README — they are
   retrieved by fingerprint, not by README browsing.

**Topical entry format**:

`<NAME>/<N>/<slug>.md`:
```
# <Short title>

<body — keep it self-contained; the agent that retrieves this should be able to
act on it without reading the README.md>
```

`<NAME>/<N>/<slug>.fingerprint` (JSON, two fields):
```json
{{
  "semantic_description": "<1-2 sentence summary of when this experience applies>",
  "keywords": {{
    "problem_kind": "<one of doc/retrieval/INDEX.md §7 controlled vocab>",
    "data": "<one of doc/retrieval/INDEX.md §7 controlled vocab>",
    "pattern": "<one of doc/retrieval/INDEX.md §7 controlled vocab>"
  }}
}}
```

A keyword value may be an array if the experience covers multiple classes.

Capture TWO kinds of reusable lesson:
1. Correctness — how to produce a result that actually verifies (which annotations /
   proof obligations matter, valid `proof_auto.v` vs `proof_manual.v`, what counts
   as cheating).
2. Efficiency — what made this run SLOW or wasteful (retries, dead-end fixes,
   re-deriving something that already existed, a critic re-run, time spent
   re-discovering a convention), and the reusable shortcut that avoids it next time
   (e.g. "use the four-field fingerprint", "don't try X, it never works",
   "recognize convention Y up front"). File these on the same surface (README §
   or numbered topical entry) as the topic they concern.

Hard rules:
- Touch nothing outside `experiences/general/`.
- Only record reusable rules, not task-specific anecdotes.
- If an existing rule in README.md or a topical entry should be sharpened, edit
  it in place instead of appending a near-duplicate.
- If this run taught nothing general, leave the experience files unchanged.
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
