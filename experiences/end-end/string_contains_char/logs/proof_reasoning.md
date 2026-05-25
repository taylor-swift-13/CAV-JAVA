# Proof Reasoning

## 2026-04-22 manual witnesses after successful `symexec`

Generated manual file: `output/verify_20260422_234921_string_contains_char/coq/generated/string_contains_char_proof_manual.v`.

After the annotated loop invariant was accepted by `symexec`, the generated manual file still contained four admitted obligations:

```coq
Lemma proof_of_string_contains_char_entail_wit_1 : string_contains_char_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_contains_char_entail_wit_2 : string_contains_char_entail_wit_2.
Proof. Admitted.
Lemma proof_of_string_contains_char_return_wit_1 : string_contains_char_return_wit_1.
Proof. Admitted.
Lemma proof_of_string_contains_char_return_wit_2 : string_contains_char_return_wit_2.
Proof. Admitted.
```

The corresponding goals in `string_contains_char_goal.v` are all pure list/spec bridge obligations plus the unchanged `CharArray.full` resource:

```coq
Definition string_contains_char_entail_wit_2 :=
forall ... (l1_2 l2_2 : list Z) (i : Z),
  [| Znth i (l ++ 0 :: nil) 0 <> c_pre |] &&
  [| Znth i (l ++ 0 :: nil) 0 <> 0 |] &&
  [| 0 <= i |] && [| i <= n |] &&
  [| l = l1_2 ++ l2_2 |] &&
  [| Zlength l1_2 = i |] &&
  [| string_contains_char_spec l1_2 c_pre = 0 |] && ...
|-- EX l1 l2, ... [| string_contains_char_spec l1 c_pre = 0 |] ...
```

For `entail_wit_1`, the proof can choose `l1 = nil`, `l2 = l`, then `entailer!` closes the empty-prefix invariant. For `entail_wit_2`, the continuing branch gives the current character is neither zero nor `c_pre`; the proof must split `l2_2` into the current head and remaining tail, choose `l1 = l1_2 ++ [x]`, and use a helper lemma showing that appending a nonmatching character to a prefix whose spec is `0` keeps the spec at `0`.

For `return_wit_1`, the match branch has `Znth i (l ++ [0]) 0 = c_pre`. With `l = l1 ++ l2` and `Zlength l1 = i`, the suffix cannot be empty, so its head is the current matching character. A helper lemma should prove `string_contains_char_spec (l1 ++ x :: xs) c_pre = 1` when the prefix spec is `0` and `x = c_pre`.

For `return_wit_2`, the terminating-zero branch needs the standard string-scanning bridge: first derive `Zlength l = n` from `CharArray.full s_pre (n + 1) (l ++ [0])`; then show `i = n`, because if `i < n` the contract says `Znth i l 0 <> 0`, contradicting the observed zero. Once `i = n`, the length equality and `l = l1 ++ l2` force `l2 = nil`, so the prefix spec `string_contains_char_spec l1 c_pre = 0` is the full-list result.

I compared the current generated witness definitions with the archived successful run for the same program. The four witness statements are identical except for the generated workspace import path, so the proof can reuse the same conservative helper structure:

```coq
Lemma string_contains_char_spec_app_single : ...
Lemma string_contains_char_spec_app_hit : ...
```

No `Axiom` or `Admitted` will be added to `proof_manual.v`; the generated `proof_auto.v` is left untouched because those are auto-side obligations included by `goal_check.v`.
