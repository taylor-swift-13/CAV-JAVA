# Proof Reasoning

## 2026-04-23 - Return witnesses after fresh symexec

Fresh `symexec` on `annotated/verify_20260423_043145_string_starts_with_char.c` succeeded and generated three manual return obligations in `coq/generated/string_starts_with_char_proof_manual.v`:

```coq
Lemma proof_of_string_starts_with_char_return_wit_1 : string_starts_with_char_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_starts_with_char_return_wit_2 : string_starts_with_char_return_wit_2.
Proof. Admitted.

Lemma proof_of_string_starts_with_char_return_wit_3 : string_starts_with_char_return_wit_3.
Proof. Admitted.
```

The corresponding VCs in `coq/generated/string_starts_with_char_goal.v` are pure case splits over the first character of `l ++ [0]` while preserving the same `CharArray.full` resource. The key facts are:

```coq
Zlength l = n
forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0
Znth 0 (l ++ 0 :: nil) 0 = 0       (* empty-string branch *)
Znth 0 (l ++ 0 :: nil) 0 <> 0       (* nonempty branches *)
```

For `return_wit_1`, the read value is zero. If `n > 0`, `app_Znth1` rewrites the read to `Znth 0 l 0`, contradicting the no-internal-zero precondition at index `0`; therefore `n = 0`, and the third postcondition disjunct applies.

For `return_wit_2`, the read value equals `c_pre` and is nonzero. If `n = 0`, `app_Znth2` rewrites the read from `l ++ [0]` to the appended terminator, contradicting the nonzero read. Therefore `0 < n`; then `app_Znth1` rewrites the read to `Znth 0 l 0`, so the second postcondition disjunct applies.

For `return_wit_3`, the read value is nonzero and not equal to `c_pre`. The same `n > 0` argument as `return_wit_2` establishes the first postcondition disjunct, and `app_Znth1` transports the inequality to `Znth 0 l 0 <> c_pre`.

## 2026-04-23 - Fix assertion disjunction branch selectors

The first compile replay reached `proof_manual.v` after compiling `goal.v` and `proof_auto.v`, then failed at `proof_of_string_starts_with_char_return_wit_1`:

```text
File ".../string_starts_with_char_proof_manual.v", line 34, characters 9-14:
Error: Found no subterm matching "?e || ?e0" in the current goal.
```

The failing snippet was:

```coq
Right. Right.
entailer!.
```

This showed that the generated three-way assertion disjunction is parsed as `(first || second) || third`, not `first || (second || third)`. The correct branch selectors are therefore:

```coq
(* third postcondition disjunct *)
Right.

(* second postcondition disjunct *)
Left. Right.

(* first postcondition disjunct *)
Left. Left.
```

No C annotation change is needed because the VCs contain the necessary facts; this is only a proof-script selector fix.

## 2026-04-23 - Fix nonzero-read contradiction in `return_wit_2`

The next compile replay again reached `proof_manual.v` and failed in `proof_of_string_starts_with_char_return_wit_2`:

```text
File ".../string_starts_with_char_proof_manual.v", line 49, characters 6-19:
Error: No such contradiction
```

The failing branch was the `n = 0` case for proving `0 < n`. The script had rewritten the equality hypothesis

```coq
Znth 0 (l ++ 0 :: nil) 0 = c_pre
```

which only produces `0 = c_pre` and does not contradict anything. The actual contradiction must use the separate nonzero-read hypothesis:

```coq
Znth 0 (l ++ 0 :: nil) 0 <> 0
```

After `subst n`, `Zlength l = 0`, and `app_Znth2`, this hypothesis simplifies to `0 <> 0`, which closes by `contradiction`.

The first attempted fix still failed because `app_Znth2` left the hypothesis in the shape:

```coq
H0 : Znth (- Zlength l) (0 :: nil) 0 <> 0
Hz : Zlength l = 0
```

The stable script must rewrite `Hz` into the hypothesis before simplification:

```coq
rewrite Hz in H0.
simpl in H0.
contradiction.
```

The same explicit rewrite is needed in `return_wit_3`, whose nonzero-read contradiction has the same shape.
