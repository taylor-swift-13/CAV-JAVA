## Issue 1: workspace fingerprint started with empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` initially had `"semantic_description": ""` and `"keywords": {}`. The verify workflow requires these fields to be filled early, with `keywords` restricted to the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Trigger: early workspace inspection before annotation or symbolic execution.
- Localization: `output/verify_20260422_222028_set_zero/logs/workspace_fingerprint.json`.
- Fix action: after reading the retrieval index, filled the semantic description with the in-place zeroing behavior and used only controlled keywords:

```json
"algorithm_family": "simulation",
"control_flow": "for_loop",
"data_shape": "array",
"semantic_intent": "in_place_update",
"proof_pattern": ["loop_invariant", "heap_reasoning", "range_bound"],
"numeric_properties": ["nonnegative_input", "int_range"],
"edge_case_behavior": "empty_loop_possible"
```

- Result: the fingerprint now has non-empty semantic metadata. After final replay, `verification_status` was also updated to `["goal_check_passed", "proof_check_passed"]`.

## Issue 2: original annotated copy had no loop invariant for the array update

- Phenomenon: the active annotated C initially contained the bare loop:

```c
for (i = 0; i < n; ++i) {
    a[i] = 0;
}
```

Without an invariant, symbolic execution would not know that the prefix already written contains zero and that the suffix still equals the original list `l`; this semantic split is necessary for the final postcondition.

- Trigger: inspection of `annotated/verify_20260422_222028_set_zero.c` before the first `symexec` run.
- Fix action: added a loop invariant with an existential current heap list `lr`, preserving `a == a@pre`, `n@pre == Zlength(l)`, `Zlength(lr) == n@pre`, prefix-zero semantics, suffix-original semantics, and `IntArray::full(a, n@pre, lr)`. Added bridge assertions around the write:

```c
IntArray::missing_i(a, i, 0, n@pre, lr) *
data_at(a + (i * sizeof(int)), int, l[i])
```

before the store, and after the store reassembled:

```c
exists lr',
  Zlength(lr') == n@pre &&
  (forall (k: Z), (0 <= k && k < i + 1) => lr'[k] == 0) &&
  (forall (k: Z), (i + 1 <= k && k < n@pre) => lr'[k] == l[k]) &&
  IntArray::full(a, n@pre, lr')
```

- Result: rerunning `symexec` against the current annotated file completed successfully and generated fresh `set_zero_goal.v`, `set_zero_proof_auto.v`, `set_zero_proof_manual.v`, and `set_zero_goal_check.v`.

## Issue 3: one manual post-store witness remained after successful `symexec`

- Phenomenon: `symexec` succeeded, but `coq/generated/set_zero_proof_manual.v` contained one placeholder:

```coq
Lemma proof_of_set_zero_which_implies_wit_2 : set_zero_which_implies_wit_2.
Proof. Admitted.
```

- Localization: `output/verify_20260422_222028_set_zero/coq/generated/set_zero_proof_manual.v`, theorem `proof_of_set_zero_which_implies_wit_2`.
- Cause: the witness must prove that after writing zero to index `i`, the split heap `IntArray.missing_i ... lr` plus the cell `data_at(..., 0)` can be merged into `IntArray.full ... lr'`, where `lr'` is the old list updated at `i`.
- Fix action: chose `lr' = replace_Znth i 0 lr`, added local helper lemmas for `Zlength` and `Znth` over `replace_Znth`, and used `IntArray.missing_i_merge_to_full` for the heap merge:

```coq
Exists (replace_Znth i 0 lr).
entailer!.
- sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
```

The suffix branch rewrites with `Znth_replace_Znth_diff`; the prefix branch splits `k = i` from `k <> i`, using `Znth_replace_Znth_same` for the newly written cell and the old prefix hypothesis for earlier indices.

- Result: `set_zero_proof_manual.v` no longer contains `Admitted.` or a new `Axiom`, and it compiles.

## Issue 4: Coq compilation produced intermediate files that had to be cleaned

- Phenomenon: successful `coqc` replay created `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Triggering replay: from `QualifiedCProgramming/SeparationLogic`, compiled `set_zero_goal.v`, `set_zero_proof_auto.v`, `set_zero_proof_manual.v`, and `set_zero_goal_check.v` with the workspace load path `SimpleC.EE.CAV.verify_20260422_222028_set_zero`.
- Fix action: removed all non-`.v` files under the workspace `coq/` tree and checked that no workspace `input/` cleanup was needed.
- Result: `find coq input -type f` now reports only:

```text
coq/generated/set_zero_goal.v
coq/generated/set_zero_goal_check.v
coq/generated/set_zero_proof_auto.v
coq/generated/set_zero_proof_manual.v
```

Final verification replay passed `goal`, `proof_auto`, `proof_manual`, and `goal_check`.
