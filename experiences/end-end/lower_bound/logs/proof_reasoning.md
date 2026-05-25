## 2026-04-22 18:57 +0800 - Prove five lower-bound manual witnesses

After the fresh symbolic execution, `coq/generated/lower_bound_proof_manual.v` contained five admitted manual lemmas:

```coq
Lemma proof_of_lower_bound_safety_wit_2 : lower_bound_safety_wit_2.
Proof. Admitted.

Lemma proof_of_lower_bound_entail_wit_1 : lower_bound_entail_wit_1.
Proof. Admitted.

Lemma proof_of_lower_bound_entail_wit_2 : lower_bound_entail_wit_2.
Proof. Admitted.

Lemma proof_of_lower_bound_entail_wit_3_1 : lower_bound_entail_wit_3_1.
Proof. Admitted.

Lemma proof_of_lower_bound_entail_wit_3_2 : lower_bound_entail_wit_3_2.
Proof. Admitted.
```

The corresponding goals in `lower_bound_goal.v` are semantically provable from the annotation:

- `lower_bound_safety_wit_2` proves the midpoint expression `left + (right-left) ÷ 2` is in C `int` range. The context has local stores for `left` and `right`, so the proof should extract their `Int` ranges with `store_int_range`; the only nontrivial fact is `0 <= (right-left) ÷ 2 <= right-left`.
- `lower_bound_entail_wit_1` is invariant initialization. Both quantified regions are empty (`i < 0` and `n <= i < n`), so `pre_process` should solve it.
- `lower_bound_entail_wit_2` is the midpoint bridge assertion. It needs the quotient bounds plus strictness `(right-left) ÷ 2 < right-left` when `left < right`, using `Z.quot_lt`.
- `lower_bound_entail_wit_3_1` is the `a[mid] >= target` branch. The new suffix starts at `mid`; for index `j = mid`, the branch guard gives `target <= l[mid]`, and for `j > mid`, sortedness gives `l[mid] <= l[j]`.
- `lower_bound_entail_wit_3_2` is the `a[mid] < target` branch. The new prefix ends at `mid + 1`; indices below old `left` use the old prefix fact, and indices from `left` through `mid` use sortedness `l[j] <= l[mid]` plus `l[mid] < target`.

The nearest reusable proof is `examples/binary_search_first/coq/generated/binary_search_first_proof_manual.v`. Its first five manual witnesses have the same lower-bound invariant and midpoint proof shape; only the lemma names and module path differ. I will add the same local helper:

```coq
Lemma lower_bound_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
```

Then each witness can stay short: `pre_process`, explicit quotient or branch facts, `sep_apply store_int_undef_store_int` for turning `mid` into an undefined local after the branch update, and `entailer!`.
