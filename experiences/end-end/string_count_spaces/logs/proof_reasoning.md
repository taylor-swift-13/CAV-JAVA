## 2026-04-23 01:17:25 +0800 - Manual witnesses after successful symexec

Fresh `symexec` on the current active annotated file succeeded and generated:

```text
string_count_spaces_goal.v
string_count_spaces_proof_auto.v
string_count_spaces_proof_manual.v
string_count_spaces_goal_check.v
```

The generated manual proof file contains four admitted witnesses:

```coq
Lemma proof_of_string_count_spaces_entail_wit_1 : string_count_spaces_entail_wit_1.
Lemma proof_of_string_count_spaces_entail_wit_2_1 : string_count_spaces_entail_wit_2_1.
Lemma proof_of_string_count_spaces_entail_wit_2_2 : string_count_spaces_entail_wit_2_2.
Lemma proof_of_string_count_spaces_entail_wit_3 : string_count_spaces_entail_wit_3.
```

The corresponding VC shapes in `string_count_spaces_goal.v` are semantically pure list/count obligations plus preserved `CharArray.full` resources:

```coq
Definition string_count_spaces_entail_wit_2_1 :=
  ...
  [| Znth i (l ++ 0 :: nil) 0 = 32 |] &&
  [| Znth i (l ++ 0 :: nil) 0 <> 0 |] &&
  ...
  [| cnt = string_count_spaces_spec l1_2 |]
|--
  EX l1 l2,
  ...
  [| cnt + 1 = string_count_spaces_spec l1 |] && ...
```

`entail_wit_2_1` is the `s[i] == 32` branch and must extend the processed prefix by the current character while increasing `cnt`. `entail_wit_2_2` is the `s[i] != 32` branch and extends the prefix without changing `cnt`. `entail_wit_3` is the loop-exit assertion and must prove `i = n` from the zero read plus the contract fact that all characters before `n` are nonzero, then rewrite the processed prefix `l1_2` to the full list `l`.

The closest completed local proof is `examples/string_count_digits/coq/generated/string_count_digits_proof_manual.v`. The same proof pattern applies with a simpler helper lemma:

```coq
Lemma string_count_spaces_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_spaces_spec (l ++ x :: nil) =
    string_count_spaces_spec l + (if Z.eq_dec x 32 then 1 else 0).
```

The next edit will replace the generated `Admitted.` stubs in `coq/generated/string_count_spaces_proof_manual.v` with this helper and proofs copied structurally from `string_count_digits`, but using `x = 32` and `x <> 32` instead of the digit range split.

## 2026-04-23 01:18:00 +0800 - First proof compile failure and repair

Compiling through `proof_manual.v` failed at line 75:

```text
Error: No matching clauses for match.
```

The failing snippet was:

```coq
destruct l2_2.
- match goal with
  | Hnz : Znth i (l1_2 ++ nil ++ 0 :: nil) 0 <> 0 |- _ =>
      ...
  end.
```

This was not a semantic proof failure. The proof state had the expected nonzero hypothesis from the branch, but the syntactic parenthesization after `subst l` did not exactly match `l1_2 ++ nil ++ 0 :: nil`. The nearby compiled `string_count_digits` proof uses the stable generated hypothesis names (`H` for the branch predicate and `H0` for the nonzero read in these witnesses) instead of matching on the whole `Znth` term. I changed `entail_wit_2_1` and `entail_wit_2_2` to rewrite `H0` directly for the impossible empty-suffix case and rewrite `H` directly to extract either `x = 32` or `x <> 32` in the nonempty-suffix case. This keeps the proof aligned with the generated witness order and avoids brittle term-shape matching.
