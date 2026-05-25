# Proof Reasoning

## 2026-04-22 manual proof iteration 1

Fresh `symexec` succeeded on `annotated/verify_20260422_223908_string_all_lowercase.c` and generated five manual obligations in `coq/generated/string_all_lowercase_proof_manual.v`:

```coq
Lemma proof_of_string_all_lowercase_entail_wit_1 : string_all_lowercase_entail_wit_1.
Lemma proof_of_string_all_lowercase_entail_wit_2 : string_all_lowercase_entail_wit_2.
Lemma proof_of_string_all_lowercase_return_wit_1 : string_all_lowercase_return_wit_1.
Lemma proof_of_string_all_lowercase_return_wit_2 : string_all_lowercase_return_wit_2.
Lemma proof_of_string_all_lowercase_return_wit_3 : string_all_lowercase_return_wit_3.
```

The current goal file shows:

```coq
string_all_lowercase_entail_wit_2
  ... Znth i (l ++ 0 :: nil) <= 122
  ... Znth i (l ++ 0 :: nil) >= 97
  ... l = l1_2 ++ l2_2
  ... Zlength l1_2 = i
  ... string_all_lowercase_spec l1_2 = 1
|-- exists l1 l2, ... Zlength l1 = i + 1 ...
    string_all_lowercase_spec l1 = 1 ...

string_all_lowercase_return_wit_1
  ... Znth i (l ++ 0 :: nil) > 122 ...
|-- 0 = string_all_lowercase_spec l

string_all_lowercase_return_wit_2
  ... Znth i (l ++ 0 :: nil) < 97 ...
|-- 0 = string_all_lowercase_spec l

string_all_lowercase_return_wit_3
  ... Znth i (l ++ 0 :: nil) = 0 ...
|-- 1 = string_all_lowercase_spec l
```

These are the same prefix/suffix proof shape as `examples/string_all_digits/coq/generated/string_all_digits_proof_manual.v`, with the digit range `48..57` replaced by lowercase range `97..122`. The helper lemma plan is:

```coq
string_all_lowercase_spec_app_lower :
  string_all_lowercase_spec l = 1 ->
  x >= 97 /\ x <= 122 ->
  string_all_lowercase_spec (l ++ x :: nil) = 1.

string_all_lowercase_spec_app_bad_high :
  string_all_lowercase_spec l1 = 1 ->
  x > 122 ->
  string_all_lowercase_spec (l1 ++ x :: l2) = 0.

string_all_lowercase_spec_app_bad_low :
  string_all_lowercase_spec l1 = 1 ->
  x < 97 ->
  string_all_lowercase_spec (l1 ++ x :: l2) = 0.
```

`entail_wit_1` initializes the invariant by choosing `l1 = nil` and `l2 = l`. `entail_wit_2` proves the loop-step invariant by deriving that `l2_2` is nonempty, extracting its head `x`, proving `97 <= x <= 122` from the branch facts, and applying `string_all_lowercase_spec_app_lower`. `return_wit_1` and `return_wit_2` use the bad-character helper lemmas for high and low out-of-range branches. `return_wit_3` uses `CharArray.full_length` and the no-interior-zero precondition to prove `i = n`; then `l2` must be empty and the prefix spec equals the full-list spec.
