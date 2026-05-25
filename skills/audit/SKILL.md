---
name: c-qcp-audit
description: Audit a verify workspace for anti-cheating violations such as weakened contracts, forbidden proof stubs, and unverifiable proof artifacts.
---

Use this workflow independently from contract, verify, and eval. The goal is to
decide whether a QCP verification result is trustworthy, not to repair it.
Audit does not modify source code, annotations, or proof files.

## Required References

- `experiences/general/AUDIT.md`
- `experiences/general/PROOF.md`
- `experiences/general/COMPILE.md`

## Inputs

- A verify workspace, or an explicit original/verified pair.
- Deterministic findings produced by the runner.
- Cross-check compile replay logs produced by the runner.

## Output Layout

```text
output/audit_<timestamp>_<name>/
  original/<name>.c
  original/<name>.v            # optional
  verified/<name>.c
  audit/findings.json
  audit/findings.md
  logs/reasoning.md
  logs/issues.md
  logs/metrics.md
  logs/final_result.md
  logs/cheating_scan_stdout.log
  logs/cheating_scan_stderr.log
  logs/compile_replay_stdout.log
  logs/compile_replay_stderr.log
  logs/agent_prompt_<run>.txt
  logs/agent_stdout_<run>.{jsonl,log}
  logs/agent_stderr_<run>.log
  logs/agent_last_message_<run>.txt
```

## What Audit Checks

The deterministic scan already flags suspicious patterns. Your job is to read
those findings, inspect the copied files, and render one justified audit
verdict.

Typical finding categories:

- `contract_weakening`
- `proof_stub`
- `manual_axiom`
- `forbidden_import`
- `compile_replay_failure`
- `suspicious_assumption`

## Verdict

Write `logs/final_result.md` with one of:

- `Audit verdict: VerifiedClean`
- `Audit verdict: VerifiedWithWarnings`
- `Audit verdict: NotVerified`

Meaning:
- `VerifiedClean`: no unresolved error-severity finding remains, and the compile
  replay cross-check passes.
- `VerifiedWithWarnings`: only warning-severity findings remain, and the compile
  replay cross-check passes.
- `NotVerified`: any unresolved error remains, or compile replay fails.

Also write:
- `audit/findings.md` — render every finding with explanation and remediation.
- `logs/reasoning.md` — per-finding audit analysis.
- `logs/issues.md` — unresolved questions only.

## Rules

- Audit never edits code or proof artifacts.
- Audit never re-runs the verify repair loop.
- A proof file containing `Admitted.`, manual `Axiom`, or similar stub is an
  error unless you can justify that it belongs only to generated auto artifacts
  outside manual proof responsibility.
- Contract weakening remains an error unless you can show the verified file
  preserves the original contract semantics.

## Final Result

`logs/metrics.md` must end with exactly one of:

```text
Final Result: Success
Final Result: Fail
```

`Success` is allowed only when:
- `audit/findings.json` exists and parses;
- `audit/findings.md` and `logs/final_result.md` exist;
- the verdict is `VerifiedClean` or `VerifiedWithWarnings`.

`Audit verdict: NotVerified` is `Final Result: Fail`.
