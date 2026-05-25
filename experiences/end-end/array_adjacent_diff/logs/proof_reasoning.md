# Proof Reasoning

## 2026-04-22 proof iteration 1

Current generated file `coq/generated/array_adjacent_diff_proof_manual.v` contains four unfinished lemmas:
- `proof_of_array_adjacent_diff_safety_wit_4`
- `proof_of_array_adjacent_diff_entail_wit_1`
- `proof_of_array_adjacent_diff_entail_wit_2`
- `proof_of_array_adjacent_diff_return_wit_1`

Relevant generated Coq fragments:
```coq
Definition array_adjacent_diff_safety_wit_4 := ...
[| ((i + 1) < n_pre) |] && ...
[| forall (i_2: Z), (0 <= i_2 /\ i_2 < (n_pre - 1)) -> INT_MIN <= ... <= INT_MAX |] |--
[| Znth (i + 1) la 0 - Znth i la 0 <= INT_MAX |] && ...
```

The proof work is not an annotation issue: `symexec` succeeded, the invariant carries the processed prefix `l1`, and the remaining obligations are pure arithmetic/list normalization witnesses. A prior completed workspace for the same function provides a stable proof pattern: local helper `adjacent_diff_step_list` normalizes the loop-body heap update from `replace_Znth i diff (app l1 (sublist i ... lo))` to the next invariant shape `app (l1 ++ diff :: nil) (sublist (i + 1) ... lo)`.

The only adaptation needed for this workspace is in `safety_wit_4`: the current input contract states the overflow guard with range `i < n_pre - 1`, while the prior proof matched a hypothesis using `i + 1 < n_pre`. Since the loop guard gives `i + 1 < n_pre`, `lia` can derive `i < n_pre - 1`; the witness should pose the contract bound at index `i` using that derived range.

Planned proof shape:
```coq
Lemma adjacent_diff_step_list : ... .
Proof.
  ... replace_Znth_app_r ... sublist_split ... sublist_single ... replace_Znth_nothing ...
Qed.

Lemma proof_of_array_adjacent_diff_safety_wit_4 : array_adjacent_diff_safety_wit_4.
Proof.
  pre_process; entailer!;
  match goal with
  | Hdiff : forall j : Z, (0 <= j /\ j < n_pre - 1) -> _ |- _ =>
      assert (Hrange : 0 <= i /\ i < n_pre - 1) by lia;
      pose proof (Hdiff i Hrange); lia
  end.
Qed.
```

For `entail_wit_1`, instantiate the invariant prefix with `nil` and normalize `app nil (sublist 0 (n_pre - 1) lo)` to `lo` using `sublist_self`. For `entail_wit_2`, instantiate the next prefix with `l1_2 ++ diff :: nil`, use `adjacent_diff_step_list`, and split the pointwise property on `k < i_2` versus `k = i_2`. For `return_wit_1`, derive `i_3 = n_pre - 1`, rewrite `sublist_nil`, and use `l1` as the final result witness.

