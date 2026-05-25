# Proof reasoning

## 2026-04-23 manual witnesses after fresh `symexec`

Fresh `symexec` succeeded for `annotated/verify_20260423_003638_string_count_digits.c` and generated five manual obligations in `coq/generated/string_count_digits_proof_manual.v`:

```coq
Lemma proof_of_string_count_digits_entail_wit_1 : string_count_digits_entail_wit_1.
Lemma proof_of_string_count_digits_entail_wit_2_1 : string_count_digits_entail_wit_2_1.
Lemma proof_of_string_count_digits_entail_wit_2_2 : string_count_digits_entail_wit_2_2.
Lemma proof_of_string_count_digits_entail_wit_2_3 : string_count_digits_entail_wit_2_3.
Lemma proof_of_string_count_digits_entail_wit_3 : string_count_digits_entail_wit_3.
```

The generated VCs are semantically provable from the current invariant. `entail_wit_1` initializes the prefix split with `l1 = nil`, `l2 = l`. The three `entail_wit_2_*` obligations extend the processed prefix by the current nonzero character and differ only by branch facts:

```coq
(* digit branch *)
Znth i (l ++ 0 :: nil) 0 <= 57
Znth i (l ++ 0 :: nil) 0 >= 48

(* non-digit branches *)
Znth i (l ++ 0 :: nil) 0 < 48
Znth i (l ++ 0 :: nil) 0 > 57
```

Each preservation proof must first show `i < n`; if `i = n`, then reading a nonzero current character contradicts the sentinel at index `n`. After `i < n`, `l2_2` cannot be empty, so destructing it exposes the current character `x` and suffix `xs`. The chosen witnesses are `l1_2 ++ x :: nil` and `xs`. The missing pure fact is the append-last equation for the spec:

```coq
string_count_digits_spec (l ++ x :: nil) =
  string_count_digits_spec l +
  (if Z_le_dec 48 x then if Z_le_dec x 57 then 1 else 0 else 0)
```

`entail_wit_3` is the loop-exit bridge. From `Znth i (l ++ 0 :: nil) 0 = 0`, bounds, and the contract fact that all logical string elements below `n` are nonzero, prove `i = n`. Then `Zlength l1_2 = n`, `Zlength l = n`, and `l = l1_2 ++ l2_2` force `l1_2 = l`; this gives `cnt = string_count_digits_spec l` for the post-loop assertion. No new axiom is needed; all remaining obligations are list decomposition and arithmetic.

## 2026-04-23 compile failure in first `entail_wit_2_1` proof

The first full compile replay reached `string_count_digits_proof_manual.v` after compiling `string_count_digits.v`, `string_count_digits_goal.v`, and `string_count_digits_proof_auto.v`, then failed with:

```text
File ".../string_count_digits_proof_manual.v", line 68, characters 6-303:
Error: No matching clauses for match.
```

The failing proof fragment matched both `Zlength l1_2 = n` and `Znth n (l ++ 0 :: nil) 0 <> 0`, but the prefix-length hypothesis is unnecessary for the sentinel contradiction. At that point the proof already has `i = n` and `Hlen_l : Zlength l = n`; the nonzero current-character hypothesis alone contradicts the sentinel at index `n` after rewriting `Znth n (l ++ 0 :: nil) 0`. I will remove the `Hpref` requirement from the match and keep only `Hnz`.

The narrowed match still failed because `subst i` rewrote `i` through `Zlength l1_2`, leaving the live nonzero hypothesis as `Znth (Zlength l1_2) (l ++ 0 :: nil) 0 <> 0` plus `Zlength l1_2 = n`. The stable fix is to avoid dependent `subst i` in these contradiction blocks. After deriving `Hi_eq : i = n`, rewrite the concrete nonzero branch hypothesis (`H1` in the digit and `>57` branches, `H0` in the `<48` branch) with `Hi_eq`, then rewrite `app_Znth2` using `Hlen_l`. This keeps the proof independent of the replacement path chosen by `subst`.

## 2026-04-23 `Znth 0` over exposed cons did not simplify automatically

After the previous fix, compile failed at line 92 with:

```text
Error: Tactic failure: Cannot find witness.
```

The live proof state for the digit branch showed the target `48 <= x` while the relevant hypothesis was:

```coq
H0 : Znth 0 (x :: xs ++ 0 :: nil) 0 >= 48
```

In this environment `simpl in H0` does not reduce `Znth 0 (x :: ...) 0` to `x`, so `lia` cannot see the arithmetic fact. I will add explicit conversion steps such as:

```coq
change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H0.
```

The same explicit conversion is needed for the `<= 57`, `< 48`, and `> 57` branch facts.

## 2026-04-23 prefix-extension witnesses need explicit append and length facts

After the `Znth 0` conversion, `proof_of_string_count_digits_entail_wit_2_1` reached `entailer!` but failed to close before `Qed`:

```text
Attempt to save an incomplete proof
(there are remaining open goals).
```

The chosen witnesses are `l1_2 ++ x :: nil` and `xs`, so the pure side needs:

```coq
l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs
Zlength (l1_2 ++ x :: nil) = i + 1
```

The closely related `string_count_char` proof carries these facts explicitly. I will add `Happ` and `Hlen_prefix` before `Exists` in each of `entail_wit_2_1`, `entail_wit_2_2`, and `entail_wit_2_3` so `entailer!` can close the equality and length side conditions.

## 2026-04-23 final proof status

After adding the append/length bridge facts, the full compile replay succeeded:

```text
compiled string_count_digits.v
compiled string_count_digits_goal.v
compiled string_count_digits_proof_auto.v
compiled string_count_digits_proof_manual.v
compiled string_count_digits_goal_check.v
```

`string_count_digits_proof_manual.v` now contains no `Admitted.` and no local `Axiom`. The remaining `Axioms` import in the prelude is the existing project import `From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap`, not a new theorem axiom added by this proof.
