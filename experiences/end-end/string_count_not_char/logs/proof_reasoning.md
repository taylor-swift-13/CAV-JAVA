# Proof Reasoning

## 2026-04-23 manual witnesses after successful `symexec`

Fresh `symexec` succeeded on `annotated/verify_20260423_005835_string_count_not_char.c` and generated:

```text
string_count_not_char_goal.v
string_count_not_char_proof_auto.v
string_count_not_char_proof_manual.v
string_count_not_char_goal_check.v
```

The generated manual proof file contains four `Admitted.` placeholders:

```coq
Lemma proof_of_string_count_not_char_entail_wit_1 : string_count_not_char_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_count_not_char_entail_wit_2_1 : string_count_not_char_entail_wit_2_1.
Proof. Admitted.
Lemma proof_of_string_count_not_char_entail_wit_2_2 : string_count_not_char_entail_wit_2_2.
Proof. Admitted.
Lemma proof_of_string_count_not_char_return_wit_1 : string_count_not_char_return_wit_1.
Proof. Admitted.
```

The goal definitions in `string_count_not_char_goal.v` show that these are pure/list obligations around the loop invariant:

```coq
Definition string_count_not_char_entail_wit_2_1 := ...
  [| Znth i (app l (cons 0 nil)) 0 <> c_pre |]
  && [| Znth i (app l (cons 0 nil)) 0 <> 0 |]
  && [| l = app l1_2 l2_2 |]
  && [| Zlength l1_2 = i |]
  && [| count = string_count_not_char_spec l1_2 c_pre |]
|--
  EX l1 l2,
  ...
  [| count + 1 = string_count_not_char_spec l1 c_pre |].
```

The first preservation witness is the `s[i] != c` branch, so the new processed prefix is `l1_2 ++ [x]` and the spec must increase by `1`. The second preservation witness is the `s[i] == c` branch, so the new processed prefix is again `l1_2 ++ [x]`, but the spec must stay equal to `count`. Both need the same prefix/suffix proof pattern used by the verified `string_contains_char` example: first prove `i < n` from the nonzero read, then destruct the current suffix `l2_2`. If the suffix is empty, the read is the terminator and contradicts `s[i] != 0`; otherwise the suffix head `x` is the current character.

The missing reusable pure facts are:

```coq
Lemma string_count_not_char_spec_app :
  forall a b c,
    string_count_not_char_spec (a ++ b) c =
    string_count_not_char_spec a c + string_count_not_char_spec b c.

Lemma string_count_not_char_spec_app_single_neq :
  forall l x c,
    x <> c ->
    string_count_not_char_spec (l ++ x :: nil) c =
    string_count_not_char_spec l c + 1.

Lemma string_count_not_char_spec_app_single_eq :
  forall l x c,
    x = c ->
    string_count_not_char_spec (l ++ x :: nil) c =
    string_count_not_char_spec l c.
```

Planned proof edit: add these helper lemmas at the top of `string_count_not_char_proof_manual.v`, prove `entail_wit_1` with `Exists nil; Exists l; entailer!`, then prove the two preservation witnesses by destructing `l2_2` and calling the single-character helper lemma for the current branch. For `return_wit_1`, first prove `i = n` from the terminating-zero read and the no-internal-zero precondition; then destruct `l2`, where the nonempty case contradicts the length equation `Zlength l = n`, and the empty case rewrites `l = l1` so `count = string_count_not_char_spec l c_pre` follows from the invariant.

## 2026-04-23 first compile failure in preservation terminator branch

The first full compile replay reached `string_count_not_char_proof_manual.v` and failed at line 79:

```text
Error: No such contradiction
```

The failing branch was inside `proof_of_string_count_not_char_entail_wit_2_1`, where the proof has just established `i = n`, rewritten the nonzero-read hypothesis through `app_Znth2`, and simplified it to a contradiction against the terminator:

```coq
rewrite app_Znth2 in H0 by lia.
replace (n - Zlength l) with 0 in H0 by lia.
simpl in H0.
contradiction.
```

The context after simplification is logically inconsistent, but `contradiction` did not pick the hypothesis reliably. I changed the terminator contradictions in both preservation witnesses to the explicit form:

```coq
exfalso.
apply H0.
reflexivity.
```

This directly uses the hypothesis `H0 : 0 <> 0` produced by simplifying the nonzero-read fact, avoiding dependency on `contradiction`'s search.

## 2026-04-23 second compile failure from substituted index shape

The next compile attempt again stopped in `proof_of_string_count_not_char_entail_wit_2_1`, now at the explicit `reflexivity` after applying `H0`. The full error showed the simplified hypothesis was not yet syntactically `0 <> 0`:

```text
H0 : Znth (Zlength l1_2 - Zlength l) (0 :: nil) 0 <> 0
Unable to unify "0" with "Znth (Zlength l1_2 - Zlength l) (0 :: nil) 0".
```

The earlier proof script tried to rewrite `n - Zlength l` to `0`, but `pre_process` had already substituted `i` using `Zlength l1_2 = i`, so the actual index expression was `Zlength l1_2 - Zlength l`. I changed both preservation witnesses to rewrite exactly that expression:

```coq
replace (Zlength l1_2 - Zlength l) with 0 in H0 by lia.
```

This should expose the terminator read as `Znth 0 (0 :: nil) 0`, allowing `simpl in H0` to produce the intended contradiction.

## 2026-04-23 return witness hypothesis-name drift

After fixing the preservation witnesses, the next compile reached `proof_of_string_count_not_char_return_wit_1` and failed at line 181:

```text
Error: Found no subterm matching "0" in the current goal.
```

The failing script was copied from a close string example and used numbered hypotheses after `entailer!`:

```coq
destruct l2.
- rewrite H2.
  rewrite app_nil_r.
  symmetry.
  exact H4.
```

This was brittle because this task's invariant has extra pure facts (`0 <= count`, `count <= i`, and `Zlength l = n`), so the generated hypothesis numbering differs from `string_contains_char`. I replaced the numbered references with shape-based matches:

```coq
match goal with
| Hshape : l = l1 ++ nil |- _ => rewrite Hshape
end;
...
match goal with
| Hcount : count = string_count_not_char_spec l1 c_pre |- _ => exact Hcount
end.
```

The nonempty suffix branch now similarly matches the concrete shape equation `l = l1 ++ x :: xs` and rewrites a matching `Zlength (l1 ++ x :: xs) = n` hypothesis before calling `lia`.

## 2026-04-23 return witness count equation direction

The next compile still stopped in the empty-suffix branch of `proof_of_string_count_not_char_return_wit_1`. A focused state check showed the invariant count fact is:

```coq
H7 : count = string_count_not_char_spec l1 c_pre
```

After rewriting `l = l1 ++ nil` and `app_nil_r`, the remaining goal already has this same direction. The previous script had an unnecessary `symmetry`, which changed the goal to the reverse equality and made the shape-based match for `count = ...` fail. I removed the `symmetry`, so the branch now closes directly with the invariant count equation.
