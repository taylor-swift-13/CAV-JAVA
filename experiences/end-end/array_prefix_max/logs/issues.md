# Issues

## Resolved

- `logs/workspace_fingerprint.json` initially needed a non-empty `semantic_description` and controlled-vocabulary `keywords`; both were added early in the run.
- A split-list loop invariant using `app` was difficult for the generated witness obligations. Replaced it with a whole-output-list invariant using a logical `lr` and semantic constraints over processed and unprocessed ranges.
- The first whole-list invariant introduced an unnecessary scalar witness for the current maximum. Removing that scalar witness reduced existential reconstruction pressure.
- `Assert ... which implies ...` syntax and explicit disjunctions inside loop annotations produced invalid or brittle generated goals. The final annotation keeps the loop body free of extra assertion bridges.
- Pre-write and post-write bridge assertions caused symbolic execution to lose local scalar facts needed for safety and preservation goals. Removing those assertions let the generated stack facts remain usable.
- Stale compiled Coq artifacts made some checks appear to target old goals. Final verification always cleaned non-`.v` files under `coq/` before recompiling.
- Manual Coq proof grouping had to match the generated invariant shape: `exists j, (range /\ equality) /\ max_property`.

## Residual

- `array_prefix_max_proof_auto.v` is generated with admits. The manual proof file has no local `Admitted`, `admit`, or `Axiom` declarations, and `array_prefix_max_goal_check.v` compiles against the generated/manual proof set.

## Retry Round 2026-04-22 07:07:49 +0800

- Retry controller re-entered the workspace after the prior run reported success, but
  `logs/continue.md` did not exist. Before any other file edits, a fresh retry section was created
  at `output/verify_20260422_063947_array_prefix_max/logs/continue.md`.
  The section records concrete workspace evidence: the active loop invariant in
  `annotated/verify_20260422_063947_array_prefix_max.c`, the successful symbolic execution line in
  `logs/qcp_run.log`, the five manual proof lemmas in
  `coq/generated/array_prefix_max_proof_manual.v`, and the empty latest compile logs.
- Fresh revalidation found no remaining theorem blocker. The following files compiled with empty
  logs using the `experiences/general/COMPILE.md` load-path template from
  `QualifiedCProgramming/SeparationLogic`:

```text
coq/generated/array_prefix_max_goal.v
coq/generated/array_prefix_max_proof_auto.v
coq/generated/array_prefix_max_proof_manual.v
coq/generated/array_prefix_max_goal_check.v
```

- The retry scan
  `rg -n "\b(Admitted|admit|Axiom)\b" coq/generated/array_prefix_max_proof_manual.v`
  returned no matches, so the manual proof still contains no local admitted proof or new axiom.
- The fresh compile created `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under
  `coq/generated/`; they were deleted after the successful compile so the workspace again contains
  only persistent `.v` sources under `coq/`.
