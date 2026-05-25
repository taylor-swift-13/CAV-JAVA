# Proof Reasoning

## Round 1: prove generated manual arithmetic witnesses

Fresh `symexec` for `annotated/verify_20260423_121024_count_digits.c` succeeded and generated four manual obligations in `coq/generated/count_digits_proof_manual.v`:

```coq
Lemma proof_of_count_digits_entail_wit_2 : count_digits_entail_wit_2.
Proof. Admitted.

Lemma proof_of_count_digits_entail_wit_3 : count_digits_entail_wit_3.
Proof. Admitted.

Lemma proof_of_count_digits_return_wit_1 : count_digits_return_wit_1.
Proof. Admitted.

Lemma proof_of_count_digits_return_wit_2 : count_digits_return_wit_2.
Proof. Admitted.
```

`proof_auto.v` owns the seven safety witnesses and `count_digits_entail_wit_1`, so I must not duplicate those theorem names in manual proof.  The earlier `count_digits_safety_wit_5` blocker is no longer manual after adding `n <= INT_MAX by local`; the generated safety context now includes `n_pre <= INT_MAX`.

Current manual VC shapes:

```coq
count_digits_entail_wit_2:
  n_pre <> 0, n_pre <= INT_MAX, 0 <= n_pre
  |-- loop invariant at cnt = 0, n = n_pre

count_digits_entail_wit_3:
  n > 0 and loop invariant before body
  |-- loop invariant after cnt + 1 and n ÷ 10

count_digits_return_wit_1:
  n_pre = 0 |-- count_digits_spec n_pre 1

count_digits_return_wit_2:
  n <= 0 and loop invariant |-- count_digits_spec n_pre cnt
```

The first and zero-return cases should be handled by `pre_process` / `entailer!` plus unfolding `count_digits_spec`.  The preservation case needs reusable arithmetic facts about positive quotient by 10 and powers of 10:

```coq
Lemma pow10_pos : forall c, 0 <= c -> 0 < 10 ^ c.
Lemma pow10_succ_mul : forall c, 0 <= c -> 10 ^ (c + 1) = 10 ^ c * 10.
Lemma div10_bounds_pos :
  forall n,
    0 < n ->
    0 <= n ÷ 10 /\
    n ÷ 10 <= n - 1 /\
    10 * (n ÷ 10) <= n /\
    n < 10 * (n ÷ 10 + 1).
```

These helpers are local to the manual proof.  They use `Z.quot` / `Z.rem` facts because generated C division is printed as `÷`, not Coq's `/`.  In `count_digits_entail_wit_3`, after `pre_process; entailer!`, the subgoals correspond to:

- quotient nonnegativity,
- `cnt + 1` nonnegativity,
- preservation of `cnt + n <= n_pre`,
- vacuous zero-count implication after increment,
- new lower digit bound `10 ^ cnt <= n_pre`,
- lower interval preservation using `10 * (n ÷ 10) <= n`,
- upper interval preservation using `n < 10 * (n ÷ 10 + 1)`.

The return witness for the positive-input path exits with `n <= 0` and invariant `0 <= n`, so it first proves `n = 0`.  Then `cnt > 0` follows because if `cnt = 0`, the invariant gives `n = n_pre`, contradicting `0 < n_pre` and `n = 0`.  The spec's lower bound comes from the invariant implication for positive `cnt`; the upper bound comes from the interval upper bound after rewriting `n = 0`.

## Round 2: fix stale hypothesis reference in return witness

The first full compile failed only in `proof_of_count_digits_return_wit_2`:

```text
File ".../count_digits_proof_manual.v", line 118, characters 21-24:
The term "H11" has type "0 <= 2147483647" while it is expected to have type
"cnt = 0".
```

After adding `n_pre <= INT_MAX` to the invariant, `pre_process; entailer!` introduced more pure hypotheses than the older same-function proof had.  The branch proving `cnt > 0` constructs:

```coq
assert (cnt = 0) by lia.
```

and Coq named that fact `H14`, while `H11` is now the generated pure fact `0 <= INT_MAX`.  The proof should specialize the invariant implication

```coq
H5 : cnt = 0 -> 0 = n_pre
```

with `H14`, not `H11`.  I will change only that hypothesis reference:

```coq
specialize (H5 H14).
```
