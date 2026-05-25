# Proof Reasoning

## 2026-04-23 manual initialization witness

Fresh `symexec` succeeded on the latest active annotated copy and generated one manual obligation:

```coq
Lemma proof_of_string_to_upper_ascii_entail_wit_1 : string_to_upper_ascii_entail_wit_1.
Proof. Admitted.
```

The corresponding VC is the loop-invariant initialization entailment. The left side owns the original string heap and pure precondition facts:

```coq
[| 0 <= n |] &&
[| n < INT_MAX |] &&
[| Zlength l = n |] &&
[| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |] &&
CharArray.full s_pre (n + 1) (app l (cons 0 nil))
|--
EX l2 l1, ... && CharArray.full s_pre (n + 1) (app l1 l2)
```

The invariant should be initialized by choosing `l1 = nil` for the empty processed prefix and `l2 = l ++ 0 :: nil` for the entire original payload plus terminator. With these witnesses, `app l1 l2` simplifies back to the original heap list. The uppercase-specific range facts over `97..122` are all guarded by `0 <= t < 0` at initialization, so they are vacuous. The remaining non-vacuous pure obligations are:

```coq
Zlength nil = 0
Zlength (l ++ 0 :: nil) = n + 1
forall t, 0 <= t /\ t < n -> Znth t (l ++ 0 :: nil) 0 = Znth t l 0
Znth n (l ++ 0 :: nil) 0 = 0
```

These are direct list/length facts using `Zlength_app`, `Zlength_cons`, `Zlength_nil`, `app_Znth1`, and `app_Znth2`, plus the precondition `Zlength l = n`. The proof can reuse the verified lowercase counterpart exactly because the only semantic difference, `+32` versus `-32` and different character bounds, appears only in vacuous processed-prefix clauses for this initialization witness. No helper lemma is needed.
