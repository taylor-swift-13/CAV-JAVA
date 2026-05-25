# Proof reasoning

## Manual witnesses after second `symexec`

After adding `n < INT_MAX` to the invariant and rerunning `symexec`, the manual file contains exactly three admitted obligations:

```coq
Lemma proof_of_string_find_char_entail_wit_2 : string_find_char_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_find_char_entail_wit_3 : string_find_char_entail_wit_3.
Proof. Admitted.

Lemma proof_of_string_find_char_return_wit_1 : string_find_char_return_wit_1.
Proof. Admitted.
```

`string_find_char_entail_wit_2` is the loop preservation path after both tests fail. The left side has `Znth i (l ++ 0 :: nil) 0 <> 0`, `Znth i (l ++ 0 :: nil) 0 <> c_pre`, `0 <= i`, `i <= n`, `n < INT_MAX`, `Zlength l = n`, and the old processed-prefix fact. The proof needs first to establish `i < n`; otherwise `i = n` and the appended terminator makes `Znth i (l ++ 0 :: nil) 0 = 0`, contradicting the branch fact. Once `i < n`, `app_Znth1` converts the branch facts into facts about `Znth i l 0`, and the new processed-prefix fact for `i + 1` follows by splitting on `j < i` or `j = i`.

`string_find_char_entail_wit_3` is the loop-exit assertion. The left side has `Znth i (l ++ 0 :: nil) 0 = 0`; if `i < n`, `app_Znth1` and the contract fact `forall k, 0 <= k < n -> Znth k l 0 <> 0` contradict it. Since the invariant already has `i <= n`, the only remaining case is `i = n`. Then the old prefix fact over `[0,i)` becomes the required no-match fact over `[0,n)`, and the local `i` resource can be rewritten from `i` to `n`.

`string_find_char_return_wit_1` is the found-character branch. It similarly needs `i_2 < n`, because the branch also has `Znth i_2 (l ++ 0 :: nil) 0 <> 0`. With `i_2 < n`, `app_Znth1` converts `Znth i_2 (l ++ 0 :: nil) 0 = c_pre` into `Znth i_2 l 0 = c_pre`. The postcondition disjunction should be discharged with `Left`, preserving the unchanged `CharArray.full` resource and the existing no-earlier-match prefix fact.
