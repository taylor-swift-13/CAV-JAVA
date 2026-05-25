# Verification Issues

## Issue 1: fingerprint placeholders had to be replaced early

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords`, which violates the verify workflow's early workspace-fingerprint requirement.
- Trigger: first workspace inspection showed:

```json
"semantic_description": "",
"keywords": {}
```

- Localization: `output/verify_20260422_073534_array_replace_negative_zero/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the fingerprint with a concrete semantic summary of the in-place array scan and controlled-vocabulary keywords only: `selection`, `for_loop`, `if`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `case_split`, `heap_reasoning`, `range_bound`, `int_range`, and `empty_loop_possible`. After final verification, added controlled verification status keywords `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint now has non-empty task-specific semantics and only controlled vocabulary keys/values.

## Issue 2: active annotated file initially lacked the loop invariant and exit assertion

- Phenomenon: the active annotated C initially copied the contract input exactly and had no `Inv` before the loop:

```c
for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        a[i] = 0;
    }
}
```

- Trigger: this function mutates `a` in place, and the postcondition is a per-index relation between the final array contents and original ghost list `l`. Without a loop invariant, symbolic execution would not retain a logical current-contents list or enough processed-prefix facts.
- Localization: `annotated/verify_20260422_073534_array_replace_negative_zero.c`, immediately before and after the `for` loop.
- Fix action: added an invariant with existential current contents `lc`, processed-prefix facts for negative and nonnegative original values, an untouched-suffix fact, stable `n == n@pre` / `a == a@pre`, and `IntArray::full(a, n@pre, lc)`:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < i && l[k] < 0) => lc[k] == 0) &&
      (forall (k: Z), (0 <= k && k < i && l[k] >= 0) => lc[k] == l[k]) &&
      (forall (k: Z), (i <= k && k < n@pre) => lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

Added a loop-exit assertion immediately after the loop to convert `i == n` and the prefix facts into whole-range postcondition facts before local cleanup.
- Result: reran `symexec` against the current annotated file. It succeeded and generated fresh `array_replace_negative_zero_goal.v`, `array_replace_negative_zero_proof_auto.v`, `array_replace_negative_zero_proof_manual.v`, and `array_replace_negative_zero_goal_check.v`.

## Issue 3: manual proof obligations remained after successful symexec

- Phenomenon: `symexec` succeeded, but `coq/generated/array_replace_negative_zero_proof_manual.v` contained three placeholders:

```coq
Lemma proof_of_array_replace_negative_zero_entail_wit_2_1 : array_replace_negative_zero_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_replace_negative_zero_entail_wit_2_2 : array_replace_negative_zero_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_replace_negative_zero_entail_wit_3 : array_replace_negative_zero_entail_wit_3.
Proof. Admitted.
```

- Trigger: the true branch writes the focused array cell, so the next invariant must reason about `replace_Znth i 0 lc_2`; the false branch and exit assertion require pure list/index reasoning that automation left for manual proof.
- Localization: `output/verify_20260422_073534_array_replace_negative_zero/coq/generated/array_replace_negative_zero_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_nth`/`replace_Znth` length and lookup behavior:

```coq
Lemma Zlength_replace_Znth :
  forall {A : Type} (i : Z) (x : A) (l : list A),
    Zlength (replace_Znth i x l) = Zlength l.

Lemma Znth_replace_Znth_same :
  forall {A : Type} (i : Z) (x d : A) (l : list A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i x l) d = x.

Lemma Znth_replace_Znth_diff :
  forall {A : Type} (k i : Z) (x d : A) (l : list A),
    0 <= k < Zlength l ->
    0 <= i ->
    k <> i ->
    Znth k (replace_Znth i x l) d = Znth k l d.
```

Then filled the three witness proofs. The true branch chooses `replace_Znth i 0 lc_2`; the false branch chooses `lc_2`; the exit assertion proves `i = n_pre` by `lia` and chooses `lc_2`.
- Result: `array_replace_negative_zero_proof_manual.v` compiles and contains no `Admitted.` and no top-level added `Axiom`.

## Issue 4: Coq build artifacts had to be cleaned after successful compilation

- Phenomenon: compiling generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: the verify workflow requires cleaning non-`.v` intermediate files after compilation.
- Localization: `output/verify_20260422_073534_array_replace_negative_zero/coq/generated/`.
- Fix action: after `goal_check.v` compiled successfully, ran cleanup that deleted all files under `coq/` whose names do not end in `.v`.
- Result: `coq/generated/` now contains only the four generated source files: `array_replace_negative_zero_goal.v`, `array_replace_negative_zero_proof_auto.v`, `array_replace_negative_zero_proof_manual.v`, and `array_replace_negative_zero_goal_check.v`.
