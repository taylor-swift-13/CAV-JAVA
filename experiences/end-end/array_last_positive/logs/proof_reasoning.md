# Proof reasoning

## 2026-04-22 manual entailment witnesses for `array_last_positive`

After successful `symexec`, `output/verify_20260422_053910_array_last_positive/coq/generated/array_last_positive_proof_manual.v` contains four admitted manual lemmas:

```coq
Lemma proof_of_array_last_positive_entail_wit_1 : array_last_positive_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_last_positive_entail_wit_2_1 : array_last_positive_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_last_positive_entail_wit_3 : array_last_positive_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_last_positive_return_wit_1 : array_last_positive_return_wit_1.
Proof. Admitted.
```

The corresponding goals in `array_last_positive_goal.v` are pure assertion entailments:

- `array_last_positive_entail_wit_1`: initialize the invariant after `ans = -1` and `i = 0`. The only semantic proof is vacuity of `forall j, 0 <= j < 0 -> Znth j l 0 <= 0`; arithmetic and the array resource are unchanged.
- `array_last_positive_entail_wit_2_1`: preserve the invariant in the branch where `Znth i l 0 > 0` and the C code assigns `ans = i`. The new nonnegative implication follows from the branch condition, and the suffix universal `i < j < i + 1` is empty.
- `array_last_positive_entail_wit_3`: after loop exit, `i >= n_pre` and `i <= n_pre` imply `i = n_pre`; the two guarded implications over `[0, i)` can be reused over `[0, n_pre)`.
- `array_last_positive_return_wit_1`: the final postcondition is assertion-level disjunction. From `-1 <= ans`, split on `ans = -1`; the `ans = -1` branch chooses the no-positive case, and the other branch derives `0 <= ans`, chooses the positive-index case, and uses the saved nonnegative implication.

The closest existing proof is `CAV/examples/array_find_last_equal/coq/generated/array_find_last_equal_proof_manual.v`, which has exactly the same guarded-implication structure. I will reuse that pattern with the current theorem names and the positive/nonpositive predicates. The first two witnesses should be solved by:

```coq
unfold array_last_positive_entail_wit_1.
intros.
entailer!.
```

and:

```coq
unfold array_last_positive_entail_wit_2_1.
intros.
entailer!.
```

For `entail_wit_3`, `entailer!` should expose the exit arithmetic and leave the two semantic implication goals. The proof will derive `i = n_pre` inside each remaining subgoal, then apply the saved implication hypothesis over the old upper bound `i`.

For `return_wit_1`, the script must use `pre_process` before case splitting so the pure hypotheses are available as Coq assumptions, and it must use assertion-level `Left`/`Right` for the QCP disjunction:

```coq
unfold array_last_positive_return_wit_1.
pre_process.
destruct (Z.eq_dec ans (-1)) as [Hans_eq | Hans_neq].
- Right.
  entailer!.
- assert (Hans_nonneg : 0 <= ans) by lia.
  destruct (H4 Hans_nonneg) as [Hans_val Hlast].
  Left.
  entailer!.
```
