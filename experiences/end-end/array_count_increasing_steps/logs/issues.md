# Verify Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes
- Experience updates: none

## Workspace Fingerprint

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords`.
- Trigger condition: the verify workflow requires the fingerprint to be populated early, and the user explicitly required reading `doc/retrieval/INDEX.md` first.
- Localization:
  - `output/verify_20260422_032621_array_count_increasing_steps/logs/workspace_fingerprint.json`
- Fix:
  - read `doc/retrieval/INDEX.md`
  - filled `semantic_description` with the read-only adjacent-pair counting semantics
  - used only controlled vocabulary values such as `counting`, `for_loop`, `array`, `count_iterations`, `preserve_input`, `loop_invariant`, `case_split`, `range_bound`, `int_range`, and `empty_loop_possible`
- Result:
  - the fingerprint is non-empty and now records `verification_status: goal_check_passed`.

## Annotation Layer

- Phenomenon: the input C had a `for (i = 0; i + 1 < n; ++i)` loop with no invariant, so the verifier had no loop-head summary for the processed adjacent-pair prefix.
- Trigger condition: the postcondition requires `__return == array_count_increasing_steps_spec(l)`, while the loop only maintains a scalar `cnt`.
- Localization:
  - active annotated C: `annotated/verify_20260422_032621_array_count_increasing_steps.c`
- Key original loop:

```c
int cnt = 0;

for (i = 0; i + 1 < n; ++i) {
    if (a[i] < a[i + 1]) {
        cnt++;
    }
}
```

- Fix:
  - added a loop invariant immediately before the `for` loop:

```c
/*@ Inv
      0 <= i && i <= n &&
      (0 < n => i + 1 <= n) &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l)) &&
      IntArray::full(a, n, l)
*/
```

- Why this fixes the annotation gap:
  - `cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))` records exactly the adjacent comparisons already processed at loop head.
  - `a == a@pre` and `n == n@pre` preserve the unchanged input state needed by the postcondition.
  - `0 < n => i + 1 <= n` is the frontend-compatible loop-head fact needed for signed safety of the guard expression `i + 1`.
- Result:
  - `symexec` accepted the annotation and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Symexec Invocation

- Phenomenon: the workspace initially had no generated Coq files under `coq/generated/`.
- Trigger condition: this was a fresh verify workspace and the annotation had just changed.
- Command shape used:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_032621_array_count_increasing_steps.c \
  --goal-file=output/verify_20260422_032621_array_count_increasing_steps/coq/generated/array_count_increasing_steps_goal.v \
  --proof-auto-file=output/verify_20260422_032621_array_count_increasing_steps/coq/generated/array_count_increasing_steps_proof_auto.v \
  --proof-manual-file=output/verify_20260422_032621_array_count_increasing_steps/coq/generated/array_count_increasing_steps_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_032621_array_count_increasing_steps \
  --no-exec-info
```

- Key log excerpt from `logs/qcp_run.log`:

```text
Symbolic Execution into function array_count_increasing_steps
End of symbolic execution of function array_count_increasing_steps
Successfully finished symbolic execution
```

- Result:
  - `symexec` exited with status `0`.

## Manual Proof

- Phenomenon: generated `array_count_increasing_steps_proof_manual.v` contained five `Admitted.` witness stubs:
  - `proof_of_array_count_increasing_steps_safety_wit_7`
  - `proof_of_array_count_increasing_steps_entail_wit_1`
  - `proof_of_array_count_increasing_steps_entail_wit_2_1`
  - `proof_of_array_count_increasing_steps_entail_wit_2_2`
  - `proof_of_array_count_increasing_steps_return_wit_1`
- Trigger condition: the remaining obligations were pure list/arithmetic facts about prefix step counts that auto proof did not discharge.
- Localization:
  - `output/verify_20260422_032621_array_count_increasing_steps/coq/generated/array_count_increasing_steps_proof_manual.v`
- Fix:
  - added helper lemmas:
    - `sublist_prefix_full`
    - `array_count_increasing_steps_spec_short`
    - `array_count_increasing_steps_spec_app_single_cons`
    - `array_count_increasing_steps_spec_app_single`
    - `array_count_increasing_steps_spec_cons_bounds`
    - `array_count_increasing_steps_spec_nonempty_bounds`
    - `array_count_increasing_steps_spec_step`
  - used the helpers to prove the five generated witness lemmas without `Admitted.`
- Representative proof bridge:

```coq
Lemma array_count_increasing_steps_spec_step :
  forall (l : list Z) (i : Z),
    0 <= i ->
    i + 1 < Zlength l ->
    array_count_increasing_steps_spec (sublist 0 (i + 2) l) =
    array_count_increasing_steps_spec (sublist 0 (i + 1) l) +
    (if Z_lt_dec (Znth i l 0) (Znth (i + 1) l 0) then 1 else 0).
```

- Result:
  - `array_count_increasing_steps_proof_manual.v` compiled.
  - `array_count_increasing_steps_goal_check.v` compiled.
  - direct grep found no `Admitted.` and no proof-level `Axiom` declarations in `proof_manual.v`.

## Compile And Cleanup

- Compile order used from `QualifiedCProgramming/SeparationLogic`:
  - `original/array_count_increasing_steps.v`
  - `coq/generated/array_count_increasing_steps_goal.v`
  - `coq/generated/array_count_increasing_steps_proof_auto.v`
  - `coq/generated/array_count_increasing_steps_proof_manual.v`
  - `coq/generated/array_count_increasing_steps_goal_check.v`
- Result:
  - all five compile steps exited with status `0`
  - compile logs are empty because there were no warnings or errors
  - all non-`.v` files under `coq/` were deleted after validation
