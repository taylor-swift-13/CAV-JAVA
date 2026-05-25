# Proof Reasoning

## 2026-04-22 15:41 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_153249_count_positive.c` and generated `coq/generated/count_positive_goal.v`, `count_positive_proof_auto.v`, `count_positive_proof_manual.v`, and `count_positive_goal_check.v`. The generated manual file contains five admitted obligations:

```coq
Lemma proof_of_count_positive_safety_wit_4 : count_positive_safety_wit_4.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_1 : count_positive_entail_wit_1.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_2_1 : count_positive_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_2_2 : count_positive_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_3 : count_positive_entail_wit_3.
Proof. Admitted.
```

The relevant goals are pure prefix-count/list obligations plus a signed-int bound:

```coq
count_positive_safety_wit_4:
  Znth i l 0 > 0, i < n_pre, cnt = count_positive_spec (sublist 0 i l)
  |-- cnt + 1 <= INT_MAX /\ INT_MIN <= cnt + 1

count_positive_entail_wit_2_1:
  Znth i l 0 > 0, cnt = count_positive_spec (sublist 0 i l)
  |-- cnt + 1 = count_positive_spec (sublist 0 (i + 1) l)

count_positive_entail_wit_2_2:
  Znth i l 0 <= 0, cnt = count_positive_spec (sublist 0 i l)
  |-- cnt = count_positive_spec (sublist 0 (i + 1) l)

count_positive_entail_wit_3:
  i >= n_pre, 0 <= i, i <= n_pre, cnt = count_positive_spec (sublist 0 i l)
  |-- i = n_pre /\ cnt = count_positive_spec l
```

The closest completed proof is `output/verify_20260422_151230_count_equal_to_k/coq/generated/count_equal_to_k_proof_manual.v`. I will reuse its pattern with predicates changed from equality-to-`k` to positivity:

1. Add `count_positive_spec_app_single`, proving the spec over `l ++ [x]` equals the old count plus `1` iff `x > 0`.
2. Add `count_positive_spec_bounds`, proving `0 <= count_positive_spec l <= Zlength l`.
3. For `safety_wit_4`, use the bounds lemma on `sublist 0 i l`; since `i < n_pre` and `n_pre` has an int range from `store_int_range`, `cnt + 1` is in signed-int range.
4. For the true and false branch entailments, rewrite `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]`, then destruct `Z_gt_dec (Znth i l 0) 0`; the current branch condition discharges the impossible case by `lia`.
5. For the exit witness, prove `i = n_pre`, rewrite `sublist 0 n_pre l` to `l` using `Zlength l = n_pre`, and finish by reflexivity.
