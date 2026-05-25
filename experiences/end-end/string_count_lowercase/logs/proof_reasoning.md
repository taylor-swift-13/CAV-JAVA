## 2026-04-23 manual witnesses after successful symexec

Generated manual proof file: `output/verify_20260423_004841_string_count_lowercase/coq/generated/string_count_lowercase_proof_manual.v`.

The latest `symexec` run succeeded and generated five manual entailment witnesses:

```coq
Lemma proof_of_string_count_lowercase_entail_wit_1 : string_count_lowercase_entail_wit_1.
Lemma proof_of_string_count_lowercase_entail_wit_2_1 : string_count_lowercase_entail_wit_2_1.
Lemma proof_of_string_count_lowercase_entail_wit_2_2 : string_count_lowercase_entail_wit_2_2.
Lemma proof_of_string_count_lowercase_entail_wit_2_3 : string_count_lowercase_entail_wit_2_3.
Lemma proof_of_string_count_lowercase_entail_wit_3 : string_count_lowercase_entail_wit_3.
```

The generated `goal.v` shows the same structure as the completed `string_count_digits` example, with only the character bounds and spec name changed. `entail_wit_2_1` is the lowercase branch (`97 <= x <= 122`) and must advance `cnt` by one. `entail_wit_2_2` is the below-range branch (`x < 97`) and `entail_wit_2_3` is the above-range branch (`x > 122`), both preserving `cnt`.

Proof plan:

- Add a local helper `string_count_lowercase_spec_app_single` proving the recursive spec over `l ++ [x]` equals the old prefix count plus the lowercase contribution for `x`.
- For `entail_wit_1`, choose `nil` and `l` for the initial prefix/suffix and let `entailer!` solve the initialized invariant.
- For each loop-body witness, use `pre_process`, recover `Zlength l = n` from `CharArray.full_length`, prove `i < n` by contradiction from the terminator read, destruct the suffix into `x :: xs`, and choose `(l1_2 ++ [x])`/`xs` as the next prefix/suffix.
- For `entail_wit_3`, prove `i = n` using the nonzero-precondition for all `0 <= k < n`, then prove `l1_2 = l` from equal length and the split `l = l1_2 ++ l2_2`; this makes `cnt == string_count_lowercase_spec l` immediate.

This proof is pure list/arithmetic plus the existing `CharArray.full_length` bridge. It does not require changing annotation or adding any `Axiom`; all generated `Admitted.` stubs in `proof_manual.v` will be replaced.
