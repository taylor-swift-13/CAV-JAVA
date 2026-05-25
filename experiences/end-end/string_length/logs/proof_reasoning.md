## 2026-04-23 proof iteration 1

Current generated manual file:

```coq
Lemma proof_of_string_length_entail_wit_2 : string_length_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_length_entail_wit_3 : string_length_entail_wit_3.
Proof. Admitted.
```

The generated goals in `coq/generated/string_length_goal.v` are semantic consequences of the loop invariant and the latest branch condition.

For `string_length_entail_wit_2`, the left side contains:

```coq
[| Znth i (l ++ 0 :: nil) 0 <> 0 |] &&
[| 0 <= i |] && [| i <= n |] &&
[| Zlength l = n |] &&
[| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |]
```

The right side needs the next invariant after `i++`, in particular `(i + 1) <= n`.  The only non-arithmetic step is proving `i < n`: if `i = n`, then `Znth n (l ++ 0 :: nil) 0` rewrites with `app_Znth2`, `Zlength l = n`, and simplification to `0`, contradicting the nonzero branch assumption.  Once `i < n`, `0 <= i + 1` and `i + 1 <= n` are pure arithmetic and `entailer!` can preserve the unchanged heap.

For `string_length_entail_wit_3`, the left side contains:

```coq
[| Znth i (l ++ 0 :: nil) 0 = 0 |] &&
[| 0 <= i |] && [| i <= n |] &&
[| Zlength l = n |] &&
[| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |] &&
((&("i")) # Int |-> i)
```

The right side is the loop-exit assertion with the local store changed to `((&("i")) # Int |-> n)`.  The needed bridge is `i = n`.  If `i < n`, `app_Znth1` rewrites the branch equality to `Znth i l 0 = 0`, contradicting the contract fact that all payload positions are nonzero.  If `i >= n`, the invariant already has `i <= n`, so `lia` gives `i = n`.  After `subst i`, `entailer!` should solve the pure facts and identical heap/local store.
