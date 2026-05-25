## 2026-04-22 08:42:41 +0800 - Manual obligations after successful symexec

Fresh `symexec` succeeded for the current annotated file `annotated/verify_20260422_084036_array_sum.c` and generated four manual placeholders in `coq/generated/array_sum_proof_manual.v`:

```coq
Lemma proof_of_array_sum_safety_wit_3 : array_sum_safety_wit_3.
Proof. Admitted.

Lemma proof_of_array_sum_entail_wit_1 : array_sum_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_sum_entail_wit_2 : array_sum_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_sum_entail_wit_3 : array_sum_entail_wit_3.
Proof. Admitted.
```

The generated goal file shows the key nontrivial safety obligation:

```coq
ret = sum (sublist 0 i l)
i < n_pre
0 <= i
i <= n_pre
n_pre <= 10000
Zlength l = n_pre
forall i_2, 0 <= i_2 /\ i_2 < n_pre ->
  -10000 <= Znth i_2 l 0 /\ Znth i_2 l 0 <= 10000
|--
ret + Znth i l 0 <= INT_MAX /\ INT_MIN <= ret + Znth i l 0
```

This is not a heap-shape problem: the array ownership is already present, and the loop invariant preserved `ret == sum(sublist 0 i l)`.  The proof needs two pure list/arithmetic facts.  First, a local `sum_bound_signed_10000` helper proves that a list whose elements are all in `[-10000,10000]` has sum between `-10000 * Zlength list` and `10000 * Zlength list`.  Second, `sum_sublist_snoc` rewrites the next prefix sum:

```coq
sum (sublist 0 (i + 1) l) =
sum (sublist 0 i l) + Znth i l 0
```

With `i + 1 <= n_pre <= 10000`, these two helpers imply the addition result is inside `[-100000000,100000000]`, which is safely within `INT_MIN..INT_MAX`.

The three entailment witnesses are the annotation-level pure transitions:

- `entail_wit_1`: initialize the invariant at `i = 0`, using `sum(sublist 0 0 l) = 0`.
- `entail_wit_2`: preserve the invariant after one iteration, using `sum_sublist_snoc`.
- `entail_wit_3`: turn loop exit `i >= n_pre` plus invariant bound `i <= n_pre` into `i = n_pre`, then rewrite `sublist 0 n_pre l` to `l`.

Planned edit: replace the four `Admitted.` placeholders in `array_sum_proof_manual.v` with helper lemmas plus direct `pre_process`/`entailer!` proofs.  No annotation change is planned because the generated VCs have the required loop semantics and heap predicates.
