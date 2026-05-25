## 2026-04-22 15:14:38 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on the active annotated file and generated `coq/generated/count_equal_to_k_goal.v`, `count_equal_to_k_proof_auto.v`, `count_equal_to_k_proof_manual.v`, and `count_equal_to_k_goal_check.v`.  The generated manual file contains five admitted obligations:

```coq
Lemma proof_of_count_equal_to_k_safety_wit_3 : count_equal_to_k_safety_wit_3.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_1 : count_equal_to_k_entail_wit_1.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_2_1 : count_equal_to_k_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_2_2 : count_equal_to_k_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_3 : count_equal_to_k_entail_wit_3.
Proof. Admitted.
```

The relevant generated goals are:

```coq
count_equal_to_k_safety_wit_3:
  Znth i l 0 = k_pre ->
  i < n_pre -> 0 <= i -> i <= n_pre ->
  ret = count_equal_to_k_spec (sublist 0 i l) k_pre ->
  0 <= n_pre -> Zlength l = n_pre ->
  ... |-- [| ret + 1 <= INT_MAX |] && [| INT_MIN <= ret + 1 |].

count_equal_to_k_entail_wit_2_1:
  same loop state plus Znth i l 0 = k_pre
  |-- ret + 1 = count_equal_to_k_spec (sublist 0 (i + 1) l) k_pre.

count_equal_to_k_entail_wit_2_2:
  same loop state plus Znth i l 0 <> k_pre
  |-- ret = count_equal_to_k_spec (sublist 0 (i + 1) l) k_pre.

count_equal_to_k_entail_wit_3:
  i >= n_pre and 0 <= i <= n_pre with prefix count state
  |-- i = n_pre && ret = count_equal_to_k_spec l k_pre.
```

This is the same proof pattern as `examples/array_count_zero/coq/generated/array_count_zero_proof_manual.v` and `output/verify_20260422_031957_array_count_greater_than_k/coq/generated/array_count_greater_than_k_proof_manual.v`.  I will add local helper lemmas:

```coq
Lemma count_equal_to_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    count_equal_to_k_spec (l ++ x :: nil) k =
    count_equal_to_k_spec l k + (if Z.eq_dec x k then 1 else 0).

Lemma count_equal_to_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= count_equal_to_k_spec l k <= Zlength l.
```

The first helper lets both branch witnesses rewrite `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]` and then split on `Z.eq_dec (Znth i l 0) k_pre`.  The second helper bounds the accumulator by the processed prefix length, which proves `ret + 1` is still inside signed-int range using `i < n_pre` and the stored range fact for `n_pre`.  The loop-exit witness will assert `i = n_pre`, rewrite the prefix `sublist 0 n_pre l` to `l` using `Zlength l = n_pre`, and finish by `entailer!`/reflexivity.
