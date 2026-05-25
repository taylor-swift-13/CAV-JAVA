# Verify Issues

## Straight-line `abs_value` required no intermediate annotations

- Phenomenon: the active annotated copy `annotated/verify_20260422_013302_abs_value.c` was identical to `input/abs_value.c`, and the function body only branches once:

```c
if (x >= 0) {
    return x;
} else {
    return -x;
}
```

- Trigger: Verify normally may need `Inv`, `Assert`, `which implies`, bridge assertions, or loop-exit assertions, but this target has no loop, no heap predicates, and no intermediate mutable state.
- Location: `annotated/verify_20260422_013302_abs_value.c`, inside `abs_value`.
- Fix action: kept the annotated C unchanged and skipped `logs/annotation_reasoning.md` because there was no concrete annotation failure to repair. Ran symbolic execution directly against the active annotated file.
- Result: `symexec` exited with status `0` and generated fresh `abs_value_goal.v`, `abs_value_proof_auto.v`, `abs_value_proof_manual.v`, and `abs_value_goal_check.v`. The relevant `logs/qcp_run.log` ending was:

```text
Symbolic Execution into function abs_value
End of symbolic execution of function abs_value
Successfully finished symbolic execution
```

## Manual proof file contained no hand-written obligations

- Phenomenon: after `symexec`, `coq/generated/abs_value_proof_manual.v` contained only imports and scope openings, with no `Lemma`, `Theorem`, or `Admitted.` body to fill.
- Trigger: this scalar branch proof generated only automatic obligations in `abs_value_proof_auto.v`; `proof_manual.v` had no manual witness definitions.
- Location: `output/verify_20260422_013302_abs_value/coq/generated/abs_value_proof_manual.v`.
- Fix action: skipped `logs/proof_reasoning.md` and did not edit `proof_manual.v`, because there was no failed manual theorem or remaining subgoal to analyze. Verified with:

```text
rg -n "\bAdmitted\.|^\s*Axiom\b" output/verify_20260422_013302_abs_value/coq/generated/abs_value_proof_manual.v
```

- Result: the search produced no matches. Full Coq compilation then succeeded for `goal`, `proof_auto`, `proof_manual`, and `goal_check`.

## Coq compilation and cleanup completed

- Phenomenon: the full compile template must be replayed even when `symexec` succeeds, and Coq compilation leaves `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Trigger: Verify success requires `goal_check.v` to compile and non-`.v` generated intermediates to be removed afterward.
- Location: `output/verify_20260422_013302_abs_value/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject`-style `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_013302_abs_value"`. Then deleted all files under this workspace's `coq/` tree whose names did not end in `.v`.
- Result: `logs/compile.log` lists successful compilation of:

```text
abs_value_goal.v
abs_value_proof_auto.v
abs_value_proof_manual.v
abs_value_goal_check.v
```

After cleanup, the only remaining files under `output/verify_20260422_013302_abs_value/coq/` are the four generated `.v` source files.
