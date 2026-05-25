# Verify Issues

## Prefix equality invariant required for array comparison

- Phenomenon: the active annotated file initially copied `input/array_equal.c` and had no `Inv` before `for (i = 0; i < n; ++i)` and no loop-exit assertion before `return 1`.
- Trigger: the contract has two semantic branches. The early `return 0` branch needs an existential mismatch witness `exists i, 0 <= i && i < n && la[i] != lb[i]`. The final `return 1` branch needs the universal equality fact `(forall (i: Z), (0 <= i && i < n) => la[i] == lb[i])`. Without an invariant, symbolic execution has no persistent record that all previously scanned positions are equal.
- Localization: [annotated/verify_20260422_035531_array_equal.c](annotated/verify_20260422_035531_array_equal.c:22).
- Fix action: after writing detailed reasoning in `logs/annotation_reasoning.md`, added a loop invariant that preserves bounds, unchanged `a`, `b`, and `n`, both `IntArray::full` resources, and the processed-prefix equality fact. Added a minimal loop-exit assertion exposing `i == n` and restating the equality fact over `[0, n)`.

Key annotation shape:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => la[j] == lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
*/
for (i = 0; i < n; ++i) {
    if (a[i] != b[i]) {
        return 0;
    }
}

/*@ Assert
      i == n &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => la[j] == lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
*/
return 1;
```

- Result: rerunning `symexec` against the updated annotated file succeeded and generated fresh `array_equal_goal.v`, `array_equal_proof_auto.v`, `array_equal_proof_manual.v`, and `array_equal_goal_check.v`.

Relevant `logs/qcp_run.log` ending:

```text
Symbolic Execution into function array_equal
End of symbolic execution of function array_equal
Successfully finished symbolic execution
symexec_status=0
```

## Manual proof phase had no obligations

- Phenomenon: after successful symbolic execution, `coq/generated/array_equal_proof_manual.v` contained only imports and scope openings, with no `Lemma`, `Theorem`, or `Admitted.` proof body to fill.
- Trigger: all generated obligations were discharged through the generated auto proof path for this simple read-only scan once the invariant and exit assertion exposed the needed prefix facts.
- Localization: [array_equal_proof_manual.v](output/verify_20260422_035531_array_equal/coq/generated/array_equal_proof_manual.v:1).
- Fix action: skipped manual proof editing and checked explicitly that `proof_manual.v` did not contain `Admitted.` or a new top-level `Axiom`.
- Result: no `logs/proof_reasoning.md` was needed.

## Full Coq compile replay and cleanup

- Phenomenon: successful `symexec` alone is not the final verification condition; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must all compile under the documented load-path template, then generated non-`.v` Coq intermediates must be removed.
- Trigger: Coq compilation produces `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files in `coq/generated/`.
- Localization: compile replay was captured in `logs/coq_compile.log`; cleanup was checked with `find output/verify_20260422_035531_array_equal/coq -type f ! -name '*.v'`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the `_CoqProject` base `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_035531_array_equal`. Then deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `array_equal_goal.v`, `array_equal_proof_auto.v`, `array_equal_proof_manual.v`, and `array_equal_goal_check.v` all compiled successfully, and no non-`.v` files remain under `coq/`.

Compile log summary:

```text
compiled=array_equal_goal.v
compiled=array_equal_proof_auto.v
compiled=array_equal_proof_manual.v
compiled=array_equal_goal_check.v
```
