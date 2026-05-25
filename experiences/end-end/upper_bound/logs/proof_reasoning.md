## 2026-04-23 05:48 +0800 - Prove manual upper-bound binary-search witnesses

Fresh `symexec` succeeded for:

```text
annotated/verify_20260423_053250_upper_bound.c
```

and generated:

```text
coq/generated/upper_bound_goal.v
coq/generated/upper_bound_proof_auto.v
coq/generated/upper_bound_proof_manual.v
coq/generated/upper_bound_goal_check.v
```

The manual file contains these admitted witnesses:

```coq
Lemma proof_of_upper_bound_safety_wit_2 : upper_bound_safety_wit_2.
Lemma proof_of_upper_bound_entail_wit_1 : upper_bound_entail_wit_1.
Lemma proof_of_upper_bound_entail_wit_2 : upper_bound_entail_wit_2.
Lemma proof_of_upper_bound_entail_wit_3_1 : upper_bound_entail_wit_3_1.
Lemma proof_of_upper_bound_entail_wit_3_2 : upper_bound_entail_wit_3_2.
```

`proof_auto.v` contains the generated auto lemmas, including `proof_of_upper_bound_return_wit_1`, so the manual proof must not define a duplicate return lemma. The current manual obligations are semantically proof-stage obligations, not annotation gaps:

- `upper_bound_safety_wit_2` proves the midpoint expression `left + (right-left) ÷ 2` remains in signed-int range. The context has `0 <= left`, `left < right`, `right <= n_pre`, and `n_pre <= INT_MAX`; it needs a small quotient-bound helper.
- `upper_bound_entail_wit_1` is invariant initialization for `left=0` and `right=n`; both quantified discarded regions are empty, so `pre_process` should solve it.
- `upper_bound_entail_wit_2` is the midpoint bridge assertion; it needs `0 <= (right-left) ÷ 2 <= right-left` and strictness `(right-left) ÷ 2 < right-left` under `left < right`.
- `upper_bound_entail_wit_3_1` is the `a[mid] > target` branch. After `right = mid`, the new suffix fact is `forall j, mid <= j < n_pre -> target_pre < Znth j l 0`; for `j = mid` it follows from the branch guard, and for `j > mid` it follows by sortedness.
- `upper_bound_entail_wit_3_2` is the `a[mid] <= target` branch. After `left = mid + 1`, the new prefix fact is `forall j, 0 <= j < mid + 1 -> Znth j l 0 <= target_pre`; old prefix indices use the invariant, and newly covered indices use sortedness up to `mid` plus the branch guard.

The nearest reusable proofs are `examples/lower_bound/coq/generated/lower_bound_proof_manual.v` and `examples/binary_search_last/coq/generated/binary_search_last_proof_manual.v`. I will add a local `upper_bound_quot2_bounds` helper and adapt their witness scripts with the upper-bound predicate directions.
