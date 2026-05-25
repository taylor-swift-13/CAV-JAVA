#!/usr/bin/env python3
"""CLI for the end-of-flow experience-consolidation unit.

Thin wrapper over ``experience_consolidate.consolidate()``: it resolves the
agent/model from ``config/agents.json`` (the ``consolidate`` model), figures out
which stage workspaces to read (explicit args or ``--auto`` discovery), runs the
consolidation agent, and reports which files under ``experiences/general/``
changed. The consolidation agent is the only writer of ``experiences/general/``.
"""
from __future__ import annotations

import argparse
import datetime as dt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import experience_consolidate

REPO_ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = REPO_ROOT / "output"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"

# Which workspace prefixes feed each scope.
SCOPE_PREFIXES: dict[str, tuple[str, ...]] = {
    "contract": ("contract_", "eval_"),
    "verify": ("verify_", "audit_"),
    "all": ("contract_", "eval_", "verify_", "audit_"),
}


def latest_workspaces(prefixes: tuple[str, ...], name: str | None) -> list[Path]:
    """Most-recent workspace dir for each prefix (optionally filtered by name)."""
    found: list[Path] = []
    for prefix in prefixes:
        candidates = [p for p in OUTPUT_ROOT.glob(f"{prefix}*") if p.is_dir()]
        if name:
            candidates = [p for p in candidates if p.name.endswith(f"_{name}")]
        if candidates:
            found.append(max(candidates, key=lambda p: p.stat().st_mtime))
    return found


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Consolidate run logs into experiences/general.")
    p.add_argument("workspaces", nargs="*", help="Stage workspace dirs to read.")
    p.add_argument("--scope", choices=["contract", "verify", "all"], default="all")
    p.add_argument("--auto", action="store_true",
                   help="Discover the latest workspace per stage for --scope.")
    p.add_argument("--name", help="With --auto, only consider workspaces ending in _<name>.")
    p.add_argument("--config", default=None)
    p.add_argument("--agent", choices=["codex", "claude"], default=None)
    p.add_argument("--model", default=None)
    p.add_argument("--reasoning-effort", default=None)
    p.add_argument("--timeout-seconds", type=int, default=600)
    p.add_argument("--dry-run", action="store_true")
    return p


def main() -> int:
    args = build_parser().parse_args()
    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.consolidate_model(DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort("medium")
    codex_bin = cfg.bin("codex", "codex")
    claude_bin = cfg.bin("claude", "claude")

    workspaces = [Path(w) if Path(w).is_absolute() else (REPO_ROOT / w) for w in args.workspaces]
    if args.auto:
        workspaces += latest_workspaces(SCOPE_PREFIXES[args.scope], args.name)
    # de-dup, keep order
    seen, ordered = set(), []
    for w in workspaces:
        rw = w.resolve()
        if rw not in seen and rw.exists():
            seen.add(rw)
            ordered.append(rw)

    if not ordered and not args.dry_run:
        print("no workspaces to consolidate (pass paths or --auto)", file=sys.stderr)
        return 2

    ts = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    logs_dir = OUTPUT_ROOT / f"consolidate_{ts}_{args.scope}" / "logs"
    print(f"[consolidate] scope={args.scope} agent={agent} model={model}", flush=True)
    for w in ordered:
        print(f"[consolidate] workspace={w}", flush=True)

    result = experience_consolidate.consolidate(
        scope=args.scope, workspaces=ordered, logs_dir=logs_dir, agent=agent,
        codex_bin=codex_bin, claude_bin=claude_bin, model=model,
        reasoning_effort=reasoning_effort, timeout_seconds=args.timeout_seconds,
        dry_run=args.dry_run,
    )
    print(f"[consolidate] ran={result.ran} detail={result.detail}", flush=True)
    if result.changed:
        print("[consolidate] changed:", flush=True)
        for name in result.changed:
            print(f"  experiences/general/{name}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
