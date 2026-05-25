## 2026-04-23 05:25 CST - Workspace fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and an empty `keywords` object.
- Trigger: the verify workflow requires the fingerprint to be filled early, and the user explicitly required reading `doc/retrieval/INDEX.md` before updating it.
- Localization: `output/verify_20260423_051744_tribonacci/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty description of scalar Tribonacci recurrence verification. The `keywords` keys and values were limited to the controlled vocabulary:

```json
"keywords": {
  "algorithm_family": "dynamic_programming",
  "control_flow": ["if", "for_loop"],
  "data_shape": "scalar_only",
  "proof_pattern": ["loop_invariant", "pure_arithmetic", "range_bound"],
  "numeric_properties": ["nonnegative_input", "overflow_guard", "int_range"],
  "edge_case_behavior": "empty_loop_possible"
}
```

- Result: the fingerprint now has independent semantic content and records the final verification status after successful replay.

## 2026-04-23 05:25 CST - Missing loop invariant for Tribonacci recurrence

- Phenomenon: the active annotated C initially matched `input/tribonacci.c` and had no invariant before `for (i = 3; i <= n; ++i)`.
- Trigger: the postcondition requires `__return == tribonacci_z(n@pre)`, but the unannotated loop did not preserve a relation between the scalar registers `(a, b, c)` and the Coq recurrence.
- Localization: `annotated/verify_20260423_051744_tribonacci.c`, immediately before the `for` loop.
- Fix action: added the loop invariant at the actual `for` control point:

```c
/*@ Inv
      2 <= n && n <= 37 &&
      n == n@pre &&
      3 <= i && i <= n + 1 &&
      a == tribonacci_z(i - 3) &&
      b == tribonacci_z(i - 2) &&
      c == tribonacci_z(i - 1)
*/
for (i = 3; i <= n; ++i) {
    d = a + b + c;
    a = b;
    b = c;
    c = d;
}
```

- Why this fixes it: after the `n == 0` and `n == 1` early returns, the continuing path has `2 <= n`. Initially `i == 3`, `a == tribonacci_z(0)`, `b == tribonacci_z(1)`, and `c == tribonacci_z(2)`. Each loop body computes the next recurrence value and shifts the three-register window. On exit, `i > n` and `i <= n + 1` imply `i == n + 1`, so `c == tribonacci_z(n)`, and `n == n@pre` bridges to the postcondition.
- Result: rerunning `symexec` on the latest annotated file succeeded and produced fresh `tribonacci_goal.v`, `tribonacci_proof_auto.v`, `tribonacci_proof_manual.v`, and `tribonacci_goal_check.v`.

## 2026-04-23 05:19 CST - Fresh symbolic execution after annotation edit

- Phenomenon: after adding the invariant, generated Coq artifacts had to be generated from the updated annotated C rather than any stale state.
- Trigger: verify workflow requires rerunning `symexec` after any invariant or assertion edit.
- Localization: `logs/qcp_run.log`.
- Fix action: created `coq/generated/`, removed any stale generated files for `tribonacci`, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260423_051744_tribonacci.c \
  --goal-file=output/verify_20260423_051744_tribonacci/coq/generated/tribonacci_goal.v \
  --proof-auto-file=output/verify_20260423_051744_tribonacci/coq/generated/tribonacci_proof_auto.v \
  --proof-manual-file=output/verify_20260423_051744_tribonacci/coq/generated/tribonacci_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_051744_tribonacci \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and `symexec_status: 0`.

## 2026-04-23 05:26 CST - Manual recurrence and range witnesses

- Phenomenon: fresh `tribonacci_proof_manual.v` contained six `Admitted.` placeholders: `proof_of_tribonacci_safety_wit_9`, `proof_of_tribonacci_safety_wit_10`, `proof_of_tribonacci_entail_wit_1`, `proof_of_tribonacci_entail_wit_2`, `proof_of_tribonacci_return_wit_1`, and `proof_of_tribonacci_return_wit_2`.
- Trigger: the automatic strategy did not prove the task-specific pure arithmetic facts for `tribonacci_z`, nor the store weakening for temporary local `d`.
- Localization: `output/verify_20260423_051744_tribonacci/coq/generated/tribonacci_proof_manual.v`.
- Fix action: imported `StoreAux`, added finite-range helper tactics and lemmas:

```coq
Lemma tribonacci_z_sum_int_bound_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    INT_MIN <= (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) <= INT_MAX.

Lemma tribonacci_z_pair_sum_int_bound_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    INT_MIN <= tribonacci_z (i - 3) + tribonacci_z (i - 2) <= INT_MAX.

Lemma tribonacci_z_step_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) = tribonacci_z i.
```

The helpers destruct the bounded index range `0..37` and reduce `tribonacci_z`. The main witnesses use `pre_process`, `entailer!`, substitution of `a`, `b`, and `c`, the helper lemmas, and `sep_apply store_int_undef_store_int` for `&( "d") # Int |-> ... |-- &( "d") # Int |-_`.
- Result: `tribonacci_proof_manual.v` compiled successfully, contains no `Admitted.`, and contains no added top-level `Axiom`.

## 2026-04-23 05:20 CST - Full Coq compile replay and cleanup

- Phenomenon: verify completion requires compiling the entire chain through `goal_check.v`, not just editing manual proof scripts.
- Trigger: `tribonacci_goal_check.v` includes both the generated auto module and the completed manual module under the workspace logical path.
- Localization: `logs/coq_compile.log`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled:

```text
original/tribonacci.v
tribonacci_goal.v
tribonacci_proof_auto.v
tribonacci_proof_manual.v
tribonacci_goal_check.v
```

using the documented base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_051744_tribonacci`.
- Result: the compile log records all five files as compiled and ends with `compile_end`. Afterward, all non-`.v` Coq build artifacts under the current workspace `coq/` directory were deleted. There were no non-`.c`/non-`.v` files in `input/` to remove.
