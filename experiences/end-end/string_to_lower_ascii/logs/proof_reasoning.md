# Proof Reasoning

## 2026-04-23 manual initialization witness

Fresh `symexec` succeeded on the latest active annotated copy and generated one manual obligation:

```coq
Lemma proof_of_string_to_lower_ascii_entail_wit_1 : string_to_lower_ascii_entail_wit_1.
Proof. Admitted.
```

The corresponding VC is the loop-invariant initialization entailment. The left side owns the original string heap:

```coq
[| 0 <= n |] &&
[| n < INT_MAX |] &&
[| Zlength l = n |] &&
[| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |] &&
CharArray.full s_pre (n + 1) (app l (cons 0 nil))
|--
EX l2 l1, ... && CharArray.full s_pre (n + 1) (app l1 l2)
```

The invariant should be initialized by choosing `l1 = nil` for the empty processed prefix and `l2 = l ++ 0 :: nil` for the entire original payload plus terminator. With these witnesses, `app l1 l2` simplifies back to the original heap list. The pure obligations are routine:

- prefix obligations over `0 <= t < 0` are vacuous;
- `Zlength nil = 0`;
- `Zlength (l ++ 0 :: nil) = n + 1`, using `Zlength l = n`;
- for `0 <= t < n`, `Znth t (l ++ 0 :: nil) 0 = Znth t l 0`, by `app_Znth1`;
- the terminator fact is `Znth n (l ++ 0 :: nil) 0 = 0`, by `app_Znth2` and index normalization.

This exactly matches the reusable initialization pattern in `examples/string_replace_char/coq/generated/string_replace_char_proof_manual.v`, so the planned proof is:

```coq
pre_process.
Exists (l ++ 0 :: nil) (@nil Z).
entailer!.
...
```

No helper lemma is needed for this witness because the remaining goals are direct `Zlength_app` / `Znth` simplifications and linear arithmetic.
