## 2026-04-22 15:27 CST - Manual proof plan for count_multiples entailment witnesses

After `symexec` succeeded, `coq/generated/count_multiples_proof_manual.v` contained four admitted manual obligations:

```coq
Lemma proof_of_count_multiples_entail_wit_1 : count_multiples_entail_wit_1.
Proof. Admitted.

Lemma proof_of_count_multiples_entail_wit_2_1 : count_multiples_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_count_multiples_entail_wit_2_2 : count_multiples_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_count_multiples_entail_wit_3 : count_multiples_entail_wit_3.
Proof. Admitted.
```

The corresponding goals in `count_multiples_goal.v` are pure arithmetic/recurrence witnesses. The branch-preservation goals have these key shapes:

```coq
[| (i % k_pre) = 0 |] ... [| cnt = count_multiples_upto_z k_pre (i - 1) |]
|--
[| cnt + 1 = count_multiples_upto_z k_pre (i + 1 - 1) |] ...
```

and

```coq
[| (i % k_pre) <> 0 |] ... [| cnt = count_multiples_upto_z k_pre (i - 1) |]
|--
[| cnt = count_multiples_upto_z k_pre (i + 1 - 1) |] ...
```

The first witness should close by `pre_process` alone because fuel zero unfolds to `0`. The two preservation witnesses need helper lemmas that expose one recursive step of `count_multiples_upto_z` at positive fuel `i`:

```coq
Lemma count_multiples_upto_z_step_multiple :
  forall k i,
    1 <= i ->
    i % k = 0 ->
    count_multiples_upto_z k i =
      count_multiples_upto_z k (i - 1) + 1.

Lemma count_multiples_upto_z_step_not_multiple :
  forall k i,
    1 <= i ->
    i % k <> 0 ->
    count_multiples_upto_z k i =
      count_multiples_upto_z k (i - 1).
```

These lemmas unfold the helper, rewrite `Z.to_nat i` as `S (Z.to_nat (i - 1))`, simplify the fixpoint, rewrite the generated last index `Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1)))` back to `i`, and then split on `Z.eq_dec (Z.rem i k) 0`. This directly matches the generated branch facts.

The exit witness has:

```coq
[| i > n_pre |] && [| i <= n_pre + 1 |] &&
[| cnt = count_multiples_upto_z k_pre (i - 1) |]
|--
[| i = n_pre + 1 |] &&
[| cnt = count_multiples_spec n_pre k_pre |]
```

Here `lia` gives `i = n_pre + 1`; after substituting, `i - 1` becomes `n_pre`, and `count_multiples_spec_as_upto_z` rewrites the postcondition into exactly the invariant summary.

## 2026-04-22 15:28 CST - Replace infix `%` in helper lemma statements with `Z.rem`

The first compile attempt reached `coq/generated/count_multiples_proof_manual.v` and failed at the helper lemma statement:

```text
File ".../count_multiples_proof_manual.v", line 35, characters 4-9:
Error: Unknown scope delimiting key k.
```

The failing source was:

```coq
Lemma count_multiples_upto_z_step_multiple :
  forall k i,
    1 <= i ->
    i % k = 0 ->
    ...
```

In ordinary Coq notation, `i % k` without parentheses is parsed as a scope delimiter rather than the generated C remainder notation. The generated VC uses parenthesized syntax `i % ( k_pre )`, but the local helper lemma is clearer and more stable if it states the condition directly as `Z.rem i k = 0`. I will change both helper lemma statements to use `Z.rem i k`; the proof body already destructs `Z.eq_dec (Z.rem i k) 0`, so no semantic change is needed.
