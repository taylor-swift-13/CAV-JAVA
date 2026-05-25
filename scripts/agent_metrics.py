#!/usr/bin/env python3
"""Shared time/token accounting for stage runners.

Every stage runner (contract, verify, eval, audit) records the same two things
in its workspace ``logs/metrics.md``:

  * wall-clock time — measured by the runner around the whole stage;
  * token usage — read from the agent CLI's own structured output.

This module owns the token side so the four runners stop carrying divergent
copies. It provides:

  * ``parse_usage(agent, path)`` — agent-aware usage extraction. ``codex`` keeps
    the last ``turn.completed.usage`` in the JSONL stream; ``claude`` reads the
    top-level ``usage`` of the single JSON object. (The old per-runner
    ``parse_usage`` was codex-only, so claude solver runs silently fell back to
    word-count approximation.)
  * ``add_usage(acc, new)`` — sum usage across rounds. Solver stages
    (contract/verify) run multiple rounds; previously only the last round's
    tokens were reported. Each round is a fresh agent session, so summing the
    per-round totals gives the stage total.
  * ``usage_lines(...)`` — render the unified key set (or the approx fallback)
    as ``metrics.md`` lines, with a single ``Agent CLI`` prefix.
  * ``read_metrics_file`` / ``write_pipeline_cost_summary`` — parse the per-stage
    ``metrics.md`` files and roll them up into one pipeline-level cost summary.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
import re


# Canonical order for token fields. codex emits ``cached_input_tokens``; claude
# emits ``cache_creation_input_tokens`` / ``cache_read_input_tokens``. We render
# whichever are present, always in this order, then any extra int fields.
UNIFIED_USAGE_KEYS = (
    "input_tokens",
    "cached_input_tokens",
    "output_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
)


def token_count(path: Path | None) -> int:
    """Whitespace word count — the approximate-token fallback when no CLI usage."""
    if path is None or not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


def parse_codex_usage(stdout_jsonl: Path | None) -> dict[str, int] | None:
    """Last ``turn.completed.usage`` object in a codex ``exec --json`` stream."""
    if stdout_jsonl is None or not stdout_jsonl.exists():
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
    if usage is None:
        return None
    return {k: v for k, v in usage.items() if isinstance(v, int)}


def parse_claude_usage(stdout_path: Path | None) -> dict[str, int] | None:
    """Token usage from a claude ``--print`` result.

    Handles both output formats:

      * ``--output-format json`` — one object with a top-level ``usage``;
      * ``--output-format stream-json`` — a JSONL event stream whose final
        ``{"type": "result", ...}`` event carries the cumulative ``usage``.
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    # --output-format json: the whole file is one object.
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        usage = obj.get("usage")
        if isinstance(usage, dict):
            return {k: v for k, v in usage.items() if isinstance(v, int)}
        return None
    # --output-format stream-json: scan for the last `result` event's usage.
    usage = None
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "result" and isinstance(ev.get("usage"), dict):
            usage = ev["usage"]
    if usage is None:
        return None
    return {k: v for k, v in usage.items() if isinstance(v, int)}


def extract_claude_last_message(stdout_path: Path | None) -> str | None:
    """Final assistant text from a claude ``--print`` result file.

    For ``--output-format json`` it is the object's ``result``; for
    ``--output-format stream-json`` it is the ``result`` event's ``result``.
    Returns None when no result text is present (caller falls back to raw stdout).
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        result = obj.get("result")
        return result if isinstance(result, str) else None
    last = None
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "result" and isinstance(ev.get("result"), str):
            last = ev["result"]
    return last


def parse_usage(agent: str, stdout_path: Path | None) -> dict[str, int] | None:
    """Dispatch usage parsing by agent backend."""
    if agent == "claude":
        return parse_claude_usage(stdout_path)
    return parse_codex_usage(stdout_path)


def add_usage(acc: dict[str, int] | None, new: dict[str, int] | None) -> dict[str, int] | None:
    """Sum two usage dicts field-by-field. None-safe; returns None iff both None."""
    if not acc and not new:
        return None
    out: dict[str, int] = dict(acc) if acc else {}
    for key, value in (new or {}).items():
        if isinstance(value, int):
            out[key] = out.get(key, 0) + value
    return out


def usage_lines(
    usage: dict[str, int] | None,
    *,
    prefix: str = "Agent CLI",
    prompt_path: Path | None = None,
    last_message_path: Path | None = None,
) -> list[str]:
    """metrics.md lines for token usage, or the approx fallback when unavailable."""
    if usage:
        ordered = [k for k in UNIFIED_USAGE_KEYS if k in usage]
        extras = sorted(k for k in usage if k not in UNIFIED_USAGE_KEYS)
        return [f"- {prefix} {key}: `{usage[key]}`" for key in (*ordered, *extras)]
    lines = []
    if prompt_path is not None:
        lines.append(f"- Approx prompt tokens: `{token_count(prompt_path)}`")
    if last_message_path is not None:
        lines.append(f"- Approx last-message tokens: `{token_count(last_message_path)}`")
    return lines


# --- pipeline roll-up -------------------------------------------------------

_STAGE_RE = re.compile(r"^- Stage:\s*`([^`]*)`")
_STATUS_RE = re.compile(r"^- Status:\s*`([^`]*)`")
_MODEL_RE = re.compile(r"^- Model:\s*`([^`]*)`")
_WALL_RE = re.compile(r"^- Wall-clock time \(seconds\):\s*`([0-9.]+)`")
# matches "- Agent CLI input_tokens: `123`" and the legacy "- Codex CLI ..." form
_USAGE_RE = re.compile(r"^- (?:Agent|Codex) CLI (\w+):\s*`(\d+)`")
_APPROX_RE = re.compile(r"^- Approx .*tokens:\s*`(\d+)`")


@dataclass
class StageMetrics:
    workspace: Path
    stage: str = "?"
    status: str | None = None
    model: str | None = None
    wall_seconds: float = 0.0
    usage: dict[str, int] = field(default_factory=dict)
    usage_is_approx: bool = False


def read_metrics_file(workspace: Path) -> StageMetrics | None:
    """Parse ``<workspace>/logs/metrics.md`` into a StageMetrics, or None."""
    metrics = workspace / "logs" / "metrics.md"
    if not metrics.exists():
        return None
    sm = StageMetrics(workspace=workspace)
    for line in metrics.read_text(encoding="utf-8", errors="replace").splitlines():
        if m := _STAGE_RE.match(line):
            sm.stage = m.group(1)
        elif m := _STATUS_RE.match(line):
            sm.status = m.group(1)
        elif m := _MODEL_RE.match(line):
            sm.model = m.group(1)
        elif m := _WALL_RE.match(line):
            sm.wall_seconds = float(m.group(1))
        elif m := _USAGE_RE.match(line):
            sm.usage[m.group(1)] = int(m.group(2))
        elif _APPROX_RE.match(line):
            sm.usage_is_approx = True
    return sm


def write_pipeline_cost_summary(workspaces: list[Path], out_path: Path) -> Path:
    """Sum wall-clock + tokens across stage workspaces into one cost_summary.md.

    Stages run serially in the pipeline, so the wall-clock total is the sum of
    per-stage wall-clock (orchestrator overhead and consolidation excluded).
    Token totals cover only stages that reported real CLI usage; stages that
    only had word-count approximations are flagged, not summed into the total.
    """
    stages: list[StageMetrics] = []
    seen: set[Path] = set()
    for ws in workspaces:
        if ws in seen:
            continue
        seen.add(ws)
        sm = read_metrics_file(ws)
        if sm is not None:
            stages.append(sm)

    total_wall = sum(s.wall_seconds for s in stages)
    total_usage: dict[str, int] | None = None
    for s in stages:
        if s.usage:
            total_usage = add_usage(total_usage, s.usage)
    approx_only = [s for s in stages if not s.usage and s.usage_is_approx]

    key_order = [k for k in UNIFIED_USAGE_KEYS if total_usage and k in total_usage]
    if total_usage:
        key_order += sorted(k for k in total_usage if k not in UNIFIED_USAGE_KEYS)

    header = ["Stage", "Model", "Status", "Wall (s)", *key_order]
    body_rows = [
        [s.stage, s.model or "?", s.status or "?", f"{s.wall_seconds:.2f}",
         *[str(s.usage.get(k, "—")) for k in key_order]]
        for s in stages
    ]
    body_rows.append([
        "**total**", "", "", f"**{total_wall:.2f}**",
        *[f"**{(total_usage or {}).get(k, 0)}**" for k in key_order],
    ])

    lines = [
        "# Pipeline Cost Summary",
        "",
        f"- Stages accounted: `{len(stages)}`",
        f"- Total wall-clock (sum of serial stages, seconds): `{total_wall:.2f}`",
    ]
    if total_usage:
        lines.append("- Total tokens: " + ", ".join(f"{k}=`{total_usage[k]}`" for k in key_order))
    else:
        lines.append("- Total tokens: `0` (no stage reported CLI usage)")
    if approx_only:
        names = ", ".join(f"{s.stage} (`{s.workspace.name}`)" for s in approx_only)
        lines.append(f"- Approx-only stages (excluded from token total): {names}")
    lines.append("")
    lines.append("| " + " | ".join(header) + " |")
    lines.append("|" + "|".join("---" for _ in header) + "|")
    for row in body_rows:
        lines.append("| " + " | ".join(row) + " |")
    lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return out_path
