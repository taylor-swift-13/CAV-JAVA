# Verify Issues

## 2026-04-22 03:29:00 +0800 - Fingerprint placeholder had to be filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was initialized before the Verify agent analyzed the program.
- Location: `output/verify_20260422_031957_array_count_greater_than_k/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the semantic description with the read-only array scan behavior and used only controlled vocabulary keywords:

```json
"algorithm_family": "counting",
"control_flow": ["for_loop", "if"],
"data_shape": "array",
"semantic_intent": ["count_iterations", "preserve_input"],
"proof_pattern": ["loop_invariant", "case_split", "range_bound", "heap_reasoning"],
"numeric_properties": ["int_range", "monotone_accumulator"],
"edge_case_behavior": "empty_loop_possible"
```

- Result: the fingerprint is now usable for retrieval and, after final verification, records `verification_status` values `goal_check_passed`, `proof_check_passed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## 2026-04-22 03:29:00 +0800 - Active C copy lacked the required prefix-count loop invariant

- Phenomenon: the active annotated file initially had the raw loop with no `Inv` or loop-exit assertion:

```c
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] > k) {
        cnt++;
    }
}

return cnt;
```

- Trigger: `array_count_greater_than_k` is a for-loop array scan. Without an invariant, symbolic execution has no loop-head state proving that `cnt` equals the number of greater-than-`k` elements in the processed prefix, nor that `a`, `n`, and `k` remain equal to their pre-state values for the final postcondition.
- Location: `annotated/verify_20260422_031957_array_count_greater_than_k.c`.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md`, then added a loop invariant at the `for` control point and a minimal loop-exit assertion:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      cnt == array_count_greater_than_k_spec(sublist(0, i, l), k) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }

/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      cnt == array_count_greater_than_k_spec(l, k@pre) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

- Result: rerunning `QualifiedCProgramming/linux-binary/symexec` with explicit output paths succeeded. `logs/qcp_run.log` contains:

```text
Symbolic Execution into function array_count_greater_than_k
End of symbolic execution of function array_count_greater_than_k
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 03:29:00 +0800 - Manual proof obligations generated after successful symexec

- Phenomenon: fresh `coq/generated/array_count_greater_than_k_proof_manual.v` contained five admitted manual obligations:

```coq
Lemma proof_of_array_count_greater_than_k_safety_wit_3 : array_count_greater_than_k_safety_wit_3.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_1 : array_count_greater_than_k_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_2_1 : array_count_greater_than_k_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_2_2 : array_count_greater_than_k_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_3 : array_count_greater_than_k_entail_wit_3.
Proof. Admitted.
```

- Trigger: the generated witnesses are pure arithmetic/list obligations: `cnt + 1` range safety, prefix extension when `Znth i l 0 > k_pre`, prefix extension when `Znth i l 0 <= k_pre`, invariant initialization on the empty prefix, and rewriting the final prefix `sublist 0 n_pre l` back to `l`.
- Location: `output/verify_20260422_031957_array_count_greater_than_k/coq/generated/array_count_greater_than_k_proof_manual.v`.
- Fix action: appended proof reasoning to `logs/proof_reasoning.md`, then added local helper lemmas for the spec over an appended singleton and for count bounds:

```coq
Lemma array_count_greater_than_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    array_count_greater_than_k_spec (l ++ x :: nil) k =
    array_count_greater_than_k_spec l k + (if Z_gt_dec x k then 1 else 0).

Lemma array_count_greater_than_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= array_count_greater_than_k_spec l k <= Zlength l.
```

- Result: `array_count_greater_than_k_proof_manual.v` compiles successfully, and `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/array_count_greater_than_k_proof_manual.v` returns no matches.

## 2026-04-22 03:29:00 +0800 - Full Coq replay and cleanup

- Phenomenon: successful `symexec` and manual proof are not sufficient by themselves; Verify success requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting Coq intermediate files.
- Trigger: `coqc` creates `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Location: `output/verify_20260422_031957_array_count_greater_than_k/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` flags, `-Q "$ORIG" ""`, and `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_031957_array_count_greater_than_k"`. The replay log `logs/compile_full.log` contains:

```text
compiled original/array_count_greater_than_k.v
compiled array_count_greater_than_k_goal.v
compiled array_count_greater_than_k_proof_auto.v
compiled array_count_greater_than_k_proof_manual.v
compiled array_count_greater_than_k_goal_check.v
compile_status=0
```

- Result: `goal_check.v` compiled successfully. All non-`.v` files under this workspace's `coq/` directory were deleted, and a follow-up `find ... -type f ! -name '*.v'` returned no files.
