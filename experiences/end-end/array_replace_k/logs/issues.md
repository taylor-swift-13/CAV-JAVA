# Issues

## Issue 1: workspace fingerprint started with empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` initially had `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires a non-empty semantic description and controlled-vocabulary keywords early in the task.
- Localization: `output/verify_20260422_072722_array_replace_k/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then updated the fingerprint to describe the in-place array replacement loop and used only controlled keys/values such as `selection`, `for_loop`, `if`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `case_split`, `heap_reasoning`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint now has a non-empty task description and controlled keywords; after final compile it also records `verification_status` as `goal_check_passed` and `proof_check_passed`.

## Issue 2: original annotated file lacked the loop invariant needed for prefix replacement

- Phenomenon: the active annotated file initially copied the contract input exactly and had no `Inv` before:

```c
for (i = 0; i < n; ++i) {
    if (a[i] == old_k) {
        a[i] = new_k;
    }
}
```

- Trigger: `symexec` needs a loop-head assertion describing the current array as an already-processed prefix plus an untouched suffix. Without that, the postcondition's elementwise final list cannot be recovered at loop exit.
- Localization: `annotated/verify_20260422_072722_array_replace_k.c`, immediately before the `for` loop.
- Fix action: added an invariant with ghost lists `l1` and `l2`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n == n@pre &&
      old_k == old_k@pre &&
      new_k == new_k@pre &&
      n@pre == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (t: Z),
        (0 <= t && t < i) =>
        ((l[t] == old_k => l1[t] == new_k) &&
         (l[t] != old_k => l1[t] == l[t]))) &&
      (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == l[i + t]) &&
      IntArray::full(a, n@pre, app(l1, l2))
*/
```

- Result: rerunning `symexec` against the current active annotated file succeeded and generated fresh `array_replace_k_goal.v`, `array_replace_k_proof_auto.v`, `array_replace_k_proof_manual.v`, and `array_replace_k_goal_check.v`.

## Issue 3: manual proof obligations remained after successful `symexec`

- Phenomenon: `symexec` succeeded, but `coq/generated/array_replace_k_proof_manual.v` contained four placeholders:

```coq
Lemma proof_of_array_replace_k_entail_wit_1 : array_replace_k_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_replace_k_entail_wit_2_1 : array_replace_k_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_replace_k_entail_wit_2_2 : array_replace_k_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_replace_k_return_wit_1 : array_replace_k_return_wit_1.
Proof. Admitted.
```

- Trigger: the invariant preservation branches require pure list reasoning: reconstruct `l2_2` as `sublist i n_pre l`, normalize either `replace_Znth i new_k_pre (l1_2 ++ l2_2)` or `l1_2 ++ l2_2`, and extend the processed-prefix property from `i` to `i + 1`.
- Localization: `output/verify_20260422_072722_array_replace_k/coq/generated/array_replace_k_proof_manual.v`.
- Fix action: adapted the successful archived `array_replace_negative_zero` proof pattern. Added local helper `list_eq_by_Znth`, proved invariant initialization with `l1 = nil`, proved the replacement branch by choosing `l1_2 ++ [new_k_pre]` and `sublist (i + 1) n_pre l`, proved the non-replacement branch by choosing `l1_2 ++ [Znth i l 0]` and the same suffix, and proved return by using `i_2 = n_pre`, `l2 = nil`, and the prefix relation.
- Result: `array_replace_k_proof_manual.v` no longer contains `Admitted.` or any new `Axiom`, and it compiles.

## Issue 4: return witness proof matched the wrong post-`pre_process` bound

- Phenomenon: the first compile replay after filling manual proofs failed in `proof_of_array_replace_k_return_wit_1` with:

```text
Error: No matching clauses for match.
```

- Trigger: the initial return proof tried to match the prefix hypothesis as bounded by `n_pre`:

```coq
match goal with
| Hprefix : forall t : Z,
    0 <= t < n_pre ->
    ... |- _ => apply Hprefix; lia
end.
```

After `pre_process`, the available hypothesis was bounded by `Zlength l1` instead:

```coq
H5 : forall t : Z,
  0 <= t < Zlength l1 ->
  (Znth t l 0 = old_k_pre -> Znth t l1 0 = new_k_pre) /\
  (Znth t l 0 <> old_k_pre -> Znth t l1 0 = Znth t l 0)
```

- Localization: `output/verify_20260422_072722_array_replace_k/coq/generated/array_replace_k_proof_manual.v`, return witness final step.
- Fix action: changed the `match goal` pattern to use `0 <= t < Zlength l1`; `lia` discharges the side condition using the generated equality `Zlength l1 = n_pre`.
- Result: the next full compile replay passed `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Issue 5: Coq intermediates had to be cleaned after successful compile

- Phenomenon: successful `coqc` compilation produced non-`.v` files under `coq/generated/`, including `.aux`, `.glob`, `.vo`, `.vok`, and `.vos`.
- Trigger: the verify workflow requires cleaning non-`.v` intermediates under `coq/` after compilation.
- Localization: `output/verify_20260422_072722_array_replace_k/coq/generated/`.
- Fix action: deleted all files under the workspace `coq/` tree whose names do not end in `.v`.
- Result: a final `find ... ! -name '*.v'` check returned no files.
