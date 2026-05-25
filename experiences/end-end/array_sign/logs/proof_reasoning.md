## Round 1: manual proof for loop-invariant initialization

Fresh `symexec` generated one manual obligation in `coq/generated/array_sign_proof_manual.v`:

```coq
Lemma proof_of_array_sign_entail_wit_1 : array_sign_entail_wit_1.
Proof. Admitted.
```

The corresponding goal `array_sign_entail_wit_1` in `array_sign_goal.v` is the initialization entailment from the function precondition to the loop invariant before the first test of `for (i = 0; i < n; ++i)`. The precondition has `IntArray.full a_pre n_pre la`, `IntArray.full out_pre n_pre lo`, `0 <= n_pre`, and both `Zlength la = n_pre` and `Zlength lo = n_pre`.

The invariant existential order is `EX l2 l1`. At initialization `i = 0`, the processed prefix should be empty and the unprocessed suffix should be the original output list, so the right witnesses are `l2 = lo` and `l1 = nil`. The generated pure obligations then reduce to `Zlength nil = 0`, `Zlength lo = n_pre`, the three sign implications over an impossible range `t < 0`, and the suffix equality `lo[t] = lo[0 + t]`. The separation part becomes exactly the original two full arrays because `app nil lo` simplifies to `lo`.

Planned proof:

```coq
unfold array_sign_entail_wit_1.
intros.
Exists lo nil.
simpl.
entailer!.
```

This is the same stable proof shape used by the prior same-task verification. I will avoid adding bullets after `entailer!` because the previous run showed that `entailer!` solves all remaining goals after these witnesses, and stale bullets cause `Wrong bullet -: No more goals`.
