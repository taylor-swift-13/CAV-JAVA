# Verification Issues

## Issue 1: workspace fingerprint started with empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and `"keywords": {}` at task start.
- Trigger: the workspace was initialized before task-specific retrieval metadata was filled in.
- Localization: `output/verify_20260422_211833_remove_duplicates_sorted/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then updated the fingerprint with a non-empty semantic description and controlled-vocabulary keywords only:

```json
"algorithm_family": "two_pointers",
"control_flow": ["if", "for_loop"],
"data_shape": ["array", "pointer"],
"semantic_intent": "in_place_update",
"proof_pattern": ["loop_invariant", "case_split", "range_bound", "heap_reasoning"]
```

- Result: the fingerprint can now be used for later retrieval without free-form keyword drift.

## Issue 2: unannotated two-pointer compaction loop had no invariant

- Phenomenon: the active annotated C initially matched `input/remove_duplicates_sorted.c`; the loop

```c
for (i = 1; i < n; ++i) {
    if (a[i] != a[j - 1]) {
        a[j] = a[i];
        j++;
    }
}
```

had no `Inv`.
- Trigger: the loop mutates the compacted prefix `a[0..j)` while still needing to read the original unprocessed suffix at index `i`. Without a loop-head summary, `symexec` would not know how `j`, the current heap list, and `remove_duplicates_sorted_spec(sublist(0, i, l))` relate.
- Localization: `annotated/verify_20260422_211833_remove_duplicates_sorted.c`, immediately before `for (i = 1; i < n; ++i)`.
- Fix action: added an invariant with existential heap list `lc`, bounds for `i` and `j`, preserved `a == a@pre` and `n == n@pre`, full-array ownership, prefix equality to `remove_duplicates_sorted_spec(sublist(0, i, l))`, and suffix preservation:

```c
/*@ Inv exists lc,
      1 <= i && i <= n@pre &&
      1 <= j && j <= i &&
      a == a@pre &&
      n == n@pre &&
      Zlength(lc) == n@pre &&
      j == Zlength(remove_duplicates_sorted_spec(sublist(0, i, l))) &&
      (forall (k: Z),
        (0 <= k && k < j) =>
        lc[k] == remove_duplicates_sorted_spec(sublist(0, i, l))[k]) &&
      (forall (k: Z),
        (i <= k && k < n@pre) =>
        lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

- Result: `symexec` completed successfully and generated fresh `remove_duplicates_sorted_goal.v`, `remove_duplicates_sorted_proof_auto.v`, `remove_duplicates_sorted_proof_manual.v`, and `remove_duplicates_sorted_goal_check.v`.

## Issue 3: manual proof needed list/spec helper lemmas

- Phenomenon: after successful symbolic execution, `coq/generated/remove_duplicates_sorted_proof_manual.v` contained five admitted obligations: `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `return_wit_1`, and `return_wit_2`.
- Trigger: the automatic proof did not prove the pure list facts for singleton initialization, appending one non-duplicate value, skipping an equal duplicate, `replace_Znth` pointwise behavior after `a[j] = a[i]`, or final prefix equality.
- Localization: `output/verify_20260422_211833_remove_duplicates_sorted/coq/generated/remove_duplicates_sorted_proof_manual.v`.
- Fix action: added local helper lemmas including `list_eq_by_Znth`, `replace_Znth_length`, `Znth_replace_Znth_eq`, `Znth_replace_Znth_other`, `rds_spec_snoc`, `rds_spec_singleton`, and `sublist_full_Zlength`, then replaced all five `Admitted.` proof bodies with `Qed` proofs.
- Result: `remove_duplicates_sorted_proof_manual.v` compiles and contains no `Admitted.` or added `Axiom`.

## Issue 4: reused exact proof had generated-name and postcondition-shape differences

- Phenomenon: the first compile attempt after adapting the existing exact proof failed with:

```text
Error: The variable j was not found in the current environment.
```

at `proof_of_remove_duplicates_sorted_entail_wit_2_1`.
- Trigger: this workspace's generated unequal-branch witness names the write index `j_2`; the reused proof script referred to `j`.
- Localization: `coq/generated/remove_duplicates_sorted_proof_manual.v`, unequal/equal branch helper setup around the `pose proof (H7 (j_2 - 1) ...)` and `replace_Znth j_2 ...` steps.
- Fix action: replaced the stale branch-local `j` references with `j_2`.
- Result: the proof advanced to the return witness.

- Second phenomenon: the next compile failed in `proof_of_remove_duplicates_sorted_return_wit_2` with:

```text
Error: Tactic failure: Cannot find witness.
```

at `rewrite Znth_sublist by lia`.
- Trigger: this task's postcondition asks for `sublist(0, j, lr) = remove_duplicates_sorted_spec(l)`, while the reused proof had targeted an explicit append decomposition. The pointwise proof needed the length of `sublist 0 j lc` to be reduced before `lia` could solve the `Znth_sublist` side condition.
- Fix action: changed the return witness to choose `lr = lc`, added `Hsub_len : Zlength (sublist 0 j lc) = j`, rewrote the pointwise index bound with `Hsub_len`, and normalized the generated index `k + 0` before applying the invariant prefix fact.
- Result: the complete compile sequence for `original/remove_duplicates_sorted.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` succeeded.

## Issue 5: Coq compilation produced intermediate files

- Phenomenon: successful `coqc` runs produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under the workspace and one auxiliary file under `input/`.
- Trigger: these are normal Coq build artifacts from compiling the generated goals and the task-specific `original/remove_duplicates_sorted.v`.
- Localization: workspace `coq/generated/`, workspace `original/`, and `input/.remove_duplicates_sorted.aux`.
- Fix action: deleted non-`.v` files under the workspace `coq/` tree, deleted non-`.c`/`.v` files under `input/`, and removed task-specific original compile byproducts.
- Result: generated Coq sources remain, while `find coq -type f ! -name '*.v'` and `find input -maxdepth 1 -type f ! -name '*.v' ! -name '*.c'` return no files.
