#!/usr/bin/env python3
"""Generic budget-driven agent loop for solver stages.

A "solver" stage (contract, verify) drives a Codex agent toward a concrete
success gate. This module owns the loop policy shared by those stages:

  * Budget: ``budget_seconds`` is the total wall-clock budget for this
    invocation. Each round gets the *remaining* budget as its timeout.
  * Restart trigger: a round is restarted **only** when the agent exited early
    without meeting the success gate and budget still remains. The retry runs in
    the same workspace and is asked to continue (see ``logs/continue.md``).
  * Timeout is failure: if a round hits its timeout, the loop stops and the
    result is ``Fail``. A timed-out agent is **not** restarted.
  * Restart context: when this invocation is itself a re-entry caused by a
    downstream critic overturning a previous result, ``restart_context`` is
    written into ``logs/continue.md`` before round 1 and handed to the first
    prompt.

The stage-specific work (build the prompt, run Codex, run the gate) lives in an
``attempt_fn`` callable supplied by each runner. This module stays free of any
contract/verify detail.
"""
from __future__ import annotations

from dataclasses import dataclass
import datetime as dt
import os
from pathlib import Path
import subprocess
from typing import Callable


# This module lives at <repo>/scripts/, so the repo root is one level up.
# Used as the agent subprocess cwd / -C dir.
REPO_ROOT = Path(__file__).resolve().parents[1]

# Returned by attempt_fn. Drives the loop's restart decision.
STATUS_SUCCESS = "Success"
STATUS_FAIL = "Fail"        # agent exited early without success -> may restart
STATUS_TIMEOUT = "Timeout"  # round hit its timeout -> stop, no restart

NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]


@dataclass
class LoopResult:
    status: str          # STATUS_SUCCESS | STATUS_FAIL
    attempts: int
    detail: str


def filter_stderr(path: Path) -> None:
    if not path.exists():
        return
    kept = [
        line
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines()
        if not any(p in line for p in NOISE_PATTERNS)
    ]
    path.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def codex_supports_reasoning_effort(codex_bin: str, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=REPO_ROOT,
            env=env,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return "--reasoning-effort" in proc.stdout


def run_codex_round(
    *,
    codex_bin: str,
    model: str,
    reasoning_effort: str,
    prompt: str,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    env: dict[str, str],
    timeout_seconds: int,
) -> tuple[int, bool]:
    """Run one Codex exec. Return (exit_code, timed_out)."""
    cmd = [
        codex_bin,
        "--dangerously-bypass-approvals-and-sandbox",
        "exec",
        "--json",
        "--skip-git-repo-check",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(last_message_path),
    ]
    if model:
        cmd.extend(["--model", model])
    if reasoning_effort and codex_supports_reasoning_effort(codex_bin, env):
        cmd.extend(["--reasoning-effort", reasoning_effort])
    cmd.append("-")
    try:
        with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                stdout=out_f,
                stderr=err_f,
                cwd=REPO_ROOT,
                env=env,
                timeout=timeout_seconds,
            )
        filter_stderr(stderr_log)
        return proc.returncode, False
    except subprocess.TimeoutExpired:
        stderr_log.write_text("Codex execution timed out.\n", encoding="utf-8")
        return 124, True


def claude_supports_flag(claude_bin: str, env: dict[str, str], flag: str) -> bool:
    try:
        proc = subprocess.run(
            [claude_bin, "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=REPO_ROOT,
            env=env,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return flag in proc.stdout


def run_claude_round(
    *,
    claude_bin: str,
    model: str,
    reasoning_effort: str,
    prompt: str,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    env: dict[str, str],
    timeout_seconds: int,
) -> tuple[int, bool]:
    """Run one Claude Code (--print) session. Return (exit_code, timed_out)."""
    cmd = [
        claude_bin,
        "--print",
        "--dangerously-skip-permissions",
        "--add-dir",
        str(REPO_ROOT),
    ]
    if model:
        cmd.extend(["--model", model])
    if reasoning_effort and claude_supports_flag(claude_bin, env, "--effort"):
        cmd.extend(["--effort", reasoning_effort])
    if claude_supports_flag(claude_bin, env, "--output-format"):
        cmd.extend(["--output-format", "json"])
    try:
        with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                stdout=out_f,
                stderr=err_f,
                cwd=REPO_ROOT,
                env=env,
                timeout=timeout_seconds,
            )
        filter_stderr(stderr_log)
        # Claude has no -o; mirror stdout into last_message for parity with codex.
        try:
            last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
        except OSError:
            pass
        return proc.returncode, False
    except subprocess.TimeoutExpired:
        stderr_log.write_text("Claude execution timed out.\n", encoding="utf-8")
        return 124, True


def run_agent_round(
    *,
    agent: str,
    codex_bin: str,
    claude_bin: str,
    model: str,
    reasoning_effort: str,
    prompt: str,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    env: dict[str, str],
    timeout_seconds: int,
) -> tuple[int, bool]:
    """Dispatch one agentic round to codex or claude. Return (exit_code, timed_out)."""
    if agent == "claude":
        return run_claude_round(
            claude_bin=claude_bin, model=model, reasoning_effort=reasoning_effort,
            prompt=prompt, stdout_jsonl=stdout_jsonl, stderr_log=stderr_log,
            last_message_path=last_message_path, env=env, timeout_seconds=timeout_seconds,
        )
    return run_codex_round(
        codex_bin=codex_bin, model=model, reasoning_effort=reasoning_effort,
        prompt=prompt, stdout_jsonl=stdout_jsonl, stderr_log=stderr_log,
        last_message_path=last_message_path, env=env, timeout_seconds=timeout_seconds,
    )


def append_continue(logs_dir: Path, kind: str, text: str) -> None:
    """Append a section to logs/continue.md (never overwrite)."""
    logs_dir.mkdir(parents=True, exist_ok=True)
    path = logs_dir / "continue.md"
    header = "# Continue Log\n\n" if not path.exists() else ""
    stamp = dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")
    section = f"## {kind} @ {stamp}\n\n{text.rstrip()}\n\n"
    with path.open("a", encoding="utf-8") as f:
        if header:
            f.write(header)
        f.write(section)


def run(
    *,
    logs_dir: Path,
    attempt_fn: Callable[[int, str | None, int], tuple[str, str]],
    budget_seconds: float,
    restart_context: str | None = None,
    emit: Callable[[str], None] | None = None,
) -> LoopResult:
    """Drive ``attempt_fn`` until success, timeout, or budget exhaustion.

    ``attempt_fn(attempt, restart_context, round_timeout)`` runs one round and
    returns ``(status, detail)`` where status is one of STATUS_*. ``round_timeout``
    is the remaining budget in whole seconds.
    """
    import time

    def _emit(msg: str) -> None:
        if emit:
            emit(msg)

    if restart_context:
        append_continue(logs_dir, "overturn", restart_context)

    start = time.time()
    attempt = 0
    detail = ""
    while True:
        remaining = budget_seconds - (time.time() - start)
        if remaining <= 0:
            _emit(f"budget_exhausted attempts={attempt}")
            return LoopResult(STATUS_FAIL, attempt, f"budget_exhausted:{detail}")
        attempt += 1
        rc = restart_context if attempt == 1 else None
        round_timeout = int(max(1, remaining))
        _emit(f"round_start attempt={attempt} round_timeout={round_timeout}")
        status, detail = attempt_fn(attempt, rc, round_timeout)

        if status == STATUS_SUCCESS:
            _emit(f"round_success attempt={attempt}")
            return LoopResult(STATUS_SUCCESS, attempt, detail)
        if status == STATUS_TIMEOUT:
            # 超时就算失败，不再启动。
            _emit(f"round_timeout attempt={attempt} (failing without restart)")
            return LoopResult(STATUS_FAIL, attempt, f"timeout:{detail}")

        # status == STATUS_FAIL: agent exited early without meeting the gate.
        if time.time() - start >= budget_seconds:
            _emit(f"budget_exhausted_after_attempt attempt={attempt}")
            return LoopResult(STATUS_FAIL, attempt, f"budget_exhausted_after_attempt:{detail}")
        append_continue(logs_dir, f"retry-after-attempt-{attempt}", detail)
        _emit(f"restarting after attempt={attempt} detail={detail}")
