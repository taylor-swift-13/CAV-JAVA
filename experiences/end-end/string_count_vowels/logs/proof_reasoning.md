## 2026-04-23 01:26:51 +0800 - Manual proof plan after fresh symexec

Fresh `symexec` on `annotated/verify_20260423_012416_string_count_vowels.c` succeeded and generated:

```text
coq/generated/string_count_vowels_goal.v
coq/generated/string_count_vowels_proof_auto.v
coq/generated/string_count_vowels_proof_manual.v
coq/generated/string_count_vowels_goal_check.v
```

`proof_manual.v` contains eight admitted manual entailment obligations:

```coq
Lemma proof_of_string_count_vowels_entail_wit_1 : string_count_vowels_entail_wit_1.
Lemma proof_of_string_count_vowels_entail_wit_2_1 : string_count_vowels_entail_wit_2_1.
Lemma proof_of_string_count_vowels_entail_wit_2_2 : string_count_vowels_entail_wit_2_2.
Lemma proof_of_string_count_vowels_entail_wit_2_3 : string_count_vowels_entail_wit_2_3.
Lemma proof_of_string_count_vowels_entail_wit_2_4 : string_count_vowels_entail_wit_2_4.
Lemma proof_of_string_count_vowels_entail_wit_2_5 : string_count_vowels_entail_wit_2_5.
Lemma proof_of_string_count_vowels_entail_wit_2_6 : string_count_vowels_entail_wit_2_6.
Lemma proof_of_string_count_vowels_entail_wit_3 : string_count_vowels_entail_wit_3.
```

The current goals are semantically provable from the loop invariant. Witness 1 initializes the invariant with `l1 = nil`, `l2 = l`, and `cnt = 0`. Witnesses 2_1 through 2_5 are the five increment-preservation branches for character values `117`, `105`, `97`, `101`, and `111`. Witness 2_6 is the non-vowel preservation branch where `cnt` stays unchanged. Witness 3 is the loop-exit assertion: from `Znth i (l ++ 0 :: nil) 0 = 0`, `0 <= i <= n`, and the precondition that every index `< n` in `l` is nonzero, prove `i = n`, then show the processed prefix `l1_2` is the full list `l`.

The reusable proof shape is the completed string-counting proof from `string_count_spaces`: first add a local append-one lemma for the recursive spec,

```coq
Lemma string_count_vowels_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_vowels_spec (l ++ x :: nil) =
    string_count_vowels_spec l +
    (if Z.eq_dec x 97 then 1
     else if Z.eq_dec x 101 then 1
     else if Z.eq_dec x 105 then 1
     else if Z.eq_dec x 111 then 1
     else if Z.eq_dec x 117 then 1
     else 0).
```

For each loop-preservation witness, the proof will:

1. Run `pre_process`, then use `prop_apply CharArray.full_length; Intros` to recover the full-array length.
2. Derive `Zlength l = n` from `Zlength (l ++ [0]) = n + 1`.
3. Prove `i < n`; otherwise `i = n`, and the current nonzero read contradicts the terminator at index `n`.
4. Substitute `l = l1_2 ++ l2_2`, destruct `l2_2`, and rule out the empty suffix because the nonzero current read would again be the terminator.
5. Rename the head of the suffix to `x`, prove the current branch condition about `x`, rewrite `string_count_vowels_spec_app_single`, choose existential witnesses `l1_2 ++ x :: nil` and `xs`, then close by `entailer!`.

This is proof work rather than annotation work: the generated VC already contains the prefix split, accumulator spec equality, nonzero invariant, and preserved `CharArray.full` resource needed for each branch.

## 2026-04-23 01:28:45 +0800 - Fix Ltac list destruct syntax after first compile

First compile replay reached `string_count_vowels_proof_manual.v` and failed before any theorem body was checked:

```text
File ".../string_count_vowels_proof_manual.v", line 79, characters 19-21:
Error:
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).
```

The failing helper fragment was:

```coq
destruct l2_2 as [| x xs];
```

Inside the `Ltac prepare_vowel_step` tactic, this list intro pattern is parsed in tactic-expression context and was rejected by the Coq parser used here. This is not a VC or annotation issue; it is proof-script syntax. I will change the helper to use a plain destruct followed by explicit renaming in the cons branch:

```coq
destruct l2_2;
...
| rename z into x;
  rename l2_2 into xs
```

The next compile should then reach the actual proof obligations and expose any semantic or hypothesis-shape mismatches.

## 2026-04-23 01:29:38 +0800 - Bind proof-context names inside Ltac patterns

The second compile still failed during Ltac parsing:

```text
File ".../string_count_vowels_proof_manual.v", line 59, characters 27-28:
Error: The reference l was not found in the current environment.
```

The issue is broader than the list destruct pattern: `Ltac prepare_vowel_step` mentioned theorem-local identifiers such as `l`, `n`, `i`, and `l1_2` directly in the tactic definition. Those names exist only after unfolding a witness theorem and running `pre_process`, so Coq rejects the tactic at definition time. I will keep the abstraction but rewrite it so each theorem-local identifier is introduced through `match goal with ...` patterns before use. The key change is from:

```coq
assert (Hlen_l : Zlength l = n) by ...
```

to:

```coq
match goal with
| Hlen : Z.of_nat (Datatypes.length (?ll ++ 0 :: nil)) = ?nn + 1 |- _ =>
    assert (Hlen_l : Zlength ll = nn) by ...
end
```

The same pattern-binding change is needed for the current index, prefix list, and current suffix head used by `expose_current_char` and `finish_vowel_step`.
