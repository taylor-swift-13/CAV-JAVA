# Verify Issues

## Empty workspace fingerprint placeholders

- Phenomenon: early workspace inspection showed `logs/workspace_fingerprint.json` still had an empty semantic description and no keywords:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the workspace had been initialized but not yet filled by a verify pass.
- Localization: `output/verify_20260422_034412_array_count_zero/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled `semantic_description` with the array zero-counting behavior and used only controlled vocabulary values: `counting`, `for_loop`, `array`, `preserve_input`, `loop_invariant`, `case_split`, `heap_reasoning`, `nonnegative_input`, `monotone_accumulator`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint is valid JSON with non-empty retrieval metadata. After final verification, `verification_status` was updated to include `goal_check_passed` and `proof_check_passed`.

## Missing loop invariant for prefix counting

- Phenomenon: the active annotated C initially matched the raw input and had no loop invariant before:

```c
for (i = 0; i < n; ++i) {
    if (a[i] == 0) {
        count++;
    }
}
```

Without an invariant, `symexec` would not have the prefix semantic fact needed to connect `count` at loop exit to `array_count_zero_spec(l)`.
- Trigger: `array_count_zero` is a for-loop array scan whose accumulator depends on the already processed prefix.
- Localization: `annotated/verify_20260422_034412_array_count_zero.c`.
- Fix action: before editing, wrote the invariant reasoning in `logs/annotation_reasoning.md`; then added:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_zero_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

and a loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_zero_spec(l) &&
      IntArray::full(a, n, l)
*/
```

- Result: the next clean `symexec` run succeeded and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual witnesses required prefix-extension helper lemmas

- Phenomenon: after successful `symexec`, `coq/generated/array_count_zero_proof_manual.v` contained five admitted manual witnesses:

```coq
proof_of_array_count_zero_safety_wit_4
proof_of_array_count_zero_entail_wit_1
proof_of_array_count_zero_entail_wit_2_1
proof_of_array_count_zero_entail_wit_2_2
proof_of_array_count_zero_entail_wit_3
```

- Trigger: the branch-preservation witnesses require showing how `array_count_zero_spec` changes when `sublist 0 i l` is extended by `Znth i l 0`; the safety witness also needs a bound showing the accumulator cannot overflow before `count++`.
- Localization: `output/verify_20260422_034412_array_count_zero/coq/generated/array_count_zero_proof_manual.v`.
- Fix action: added local helper lemmas:

```coq
Lemma array_count_zero_spec_app_single :
  forall (l : list Z) (x : Z),
    array_count_zero_spec (l ++ x :: nil) =
    array_count_zero_spec l + (if Z.eq_dec x 0 then 1 else 0).

Lemma array_count_zero_spec_bounds :
  forall (l : list Z),
    0 <= array_count_zero_spec l <= Zlength l.
```

Then replaced the five admitted proofs with scripts using `pre_process`, `entailer!`, `sublist_split`, `sublist_single`, `sublist_self`, the current branch fact `Znth i l 0 = 0` or `<> 0`, and `lia`.
- Result: `array_count_zero_proof_manual.v` compiled successfully and contains no `Admitted.` or top-level `Axiom`.

## Final compile and cleanup

- Phenomenon: final verification requires replaying the complete Coq compile sequence and then removing generated non-source artifacts under workspace `coq/`.
- Trigger: successful manual proof alone is not enough; `goal_check.v` must compile with the current `goal`, `proof_auto`, and `proof_manual`.
- Localization: compile log at `output/verify_20260422_034412_array_count_zero/logs/compile.log`.
- Fix action: compiled, from `QualifiedCProgramming/SeparationLogic`, in this order:

```text
original/array_count_zero.v
coq/generated/array_count_zero_goal.v
coq/generated/array_count_zero_proof_auto.v
coq/generated/array_count_zero_proof_manual.v
coq/generated/array_count_zero_goal_check.v
```

Then ran cleanup for non-`.v` files under `coq/`.
- Result: the full compile replay succeeded through `array_count_zero_goal_check.v`, and `find coq -type f ! -name '*.v'` returned no files.
