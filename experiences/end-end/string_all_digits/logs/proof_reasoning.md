## Proof iteration 1

Fresh `symexec` succeeded on `annotated/verify_20260422_222714_string_all_digits.c` and generated five manual obligations in `coq/generated/string_all_digits_proof_manual.v`:

```coq
Lemma proof_of_string_all_digits_entail_wit_1 : string_all_digits_entail_wit_1.
Proof. Admitted.

Lemma proof_of_string_all_digits_entail_wit_2 : string_all_digits_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_all_digits_return_wit_1 : string_all_digits_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_all_digits_return_wit_2 : string_all_digits_return_wit_2.
Proof. Admitted.

Lemma proof_of_string_all_digits_return_wit_3 : string_all_digits_return_wit_3.
Proof. Admitted.
```

The VC bodies in `string_all_digits_goal.v` correspond to the invariant split `l = l1 ++ l2`. `entail_wit_1` is invariant initialization and should choose `l1 = nil`, `l2 = l`. `entail_wit_2` is invariant preservation after one accepted digit; after `pre_process` and `CharArray.full_length`, the proof must show that the current character is the head of the remaining suffix and that appending a value in `48..57` preserves `string_all_digits_spec = 1`.

The two early return witnesses are pure semantic branches: if the current suffix head is `> 57` or `< 48`, then `string_all_digits_spec(l1 ++ x :: xs) = 0` because `string_all_digits_spec(l1) = 1` and the first bad character determines the result. The final return witness uses the break condition `Znth i (l ++ [0]) 0 = 0` and the contract fact `forall k, 0 <= k < n -> l[k] != 0` to prove `i = n`; after that, the remaining suffix must be empty and `string_all_digits_spec(l) = 1`.

I will add three local helper lemmas before the witness proofs:

```coq
string_all_digits_spec_app_digit
string_all_digits_spec_app_bad_high
string_all_digits_spec_app_bad_low
```

These helpers isolate the recursive list/spec case splits over `Z_lt_dec` and `Z_gt_dec`, keeping the witness proofs focused on `Exists`, `CharArray.full_length`, `app_Znth2`, and arithmetic side conditions. No axiom is needed and no `Admitted.` should remain in `proof_manual.v`.
