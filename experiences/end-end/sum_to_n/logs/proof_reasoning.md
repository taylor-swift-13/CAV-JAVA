## 2026-04-23 05:04 +0800 - Manual arithmetic witnesses for quotient closed form

After the first successful `symexec`, `coq/generated/sum_to_n_proof_manual.v` contains six manual witnesses:

```coq
Lemma proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Lemma proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Lemma proof_of_sum_to_n_entail_wit_1 : sum_to_n_entail_wit_1.
Lemma proof_of_sum_to_n_entail_wit_3 : sum_to_n_entail_wit_3.
Lemma proof_of_sum_to_n_entail_wit_4 : sum_to_n_entail_wit_4.
Lemma proof_of_sum_to_n_entail_wit_5 : sum_to_n_entail_wit_5.
```

All six are pure scalar arithmetic after separation-logic framing. The generated goals use `÷ 2`, i.e. Coq `Z.quot`, for the C expression `... / 2`. The key body preservation obligation is:

```coq
((i - 1) * i) ÷ 2 + i = (i * (i + 1)) ÷ 2
```

and the safety witness for `ret += i` also needs this term to be bounded by the precondition bound on `(n_pre * (n_pre + 1)) ÷ 2`. Plain `lia` or `nia` cannot solve these directly because of quotient. I tested the local helper shape in `coqtop`: prove consecutive products are even, derive exact division by `2`, then prove the triangular update with `Z.quot_unique_exact`. The reusable helper shape is:

```coq
Lemma sum_to_n_consecutive_product_even :
  forall i, Z.Even ((i - 1) * i).

Lemma sum_to_n_half_consecutive_exact :
  forall i, 2 * (((i - 1) * i) ÷ 2) = (i - 1) * i.

Lemma sum_to_n_triangular_step :
  forall i, 1 <= i ->
    ((i - 1) * i) ÷ 2 + i = (i * (i + 1)) ÷ 2.

Lemma sum_to_n_triangular_mono :
  forall i n, 0 <= i -> i <= n ->
    (i * (i + 1)) ÷ 2 <= (n * (n + 1)) ÷ 2.
```

The witness scripts will start with `pre_process; entailer!`. For `safety_wit_3`, after the heap/local framing is discharged, the proof rewrites the accumulator update with `sum_to_n_triangular_step`, uses `sum_to_n_triangular_mono` and the precondition upper bound for the `INT_MAX` side, and uses `Z.quot_pos` for the lower bound. For `entail_wit_3`, the same triangular-step equality rewrites the post-body accumulator cell to the assertion shape. The other entail witnesses should close by `lia`, `nia`, and `entailer!` after substituting the loop-exit equality `i = n_pre + 1`.

## 2026-04-23 05:06 +0800 - Fix Coq tactic grammar in helper applications

The first compile attempt failed before reaching any semantic subgoal:

```text
File ".../sum_to_n_proof_manual.v", line 45, characters 33-35:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

The failing helper proof used compact tactic syntax:

```coq
apply Z.quot_unique_exact; [lia|].
```

In this generated proof context, Coq rejected the empty second branch after the separator. I rewrote both quotient helper proofs to use explicit bullets:

```coq
apply Z.quot_unique_exact.
- lia.
pose proof (sum_to_n_half_consecutive_exact i) as Hhalf.
nia.
```

I also replaced the inline `ltac:(lia)` arguments to `sum_to_n_triangular_mono` with explicit assertions `Hnonneg_i : 0 <= i` and `Hle_in : i <= n_pre`, because that is easier to read and avoids tactic-expression parsing inside a `pose proof`.

The next compile attempt reported:

```text
File ".../sum_to_n_proof_manual.v", line 47, characters 2-58:
Error: No such goal. Focus next goal with bullet -.
```

This was not a math failure; it was another proof-script structuring issue. After `apply Z.quot_unique_exact.`, Coq expects both generated subgoals to be bullet-delimited. I changed the triangular-step proof to:

```coq
apply Z.quot_unique_exact.
- lia.
- pose proof (sum_to_n_half_consecutive_exact i) as Hhalf.
  nia.
```

The next failure was in `proof_of_sum_to_n_safety_wit_3` after `entailer!`:

```coq
n_pre, ret, i : Z
H : 1 <= i
H0 : i <= n_pre
H6 : 0 <= n_pre
H8 : n_pre * (n_pre + 1) ÷ 2 <= 2147483647
============================
-2147483648 <= i * (i + 1) ÷ 2
```

This showed that the generated pure goals are ordered as lower bound first and upper bound second. My previous bullets handled them in the opposite order, so `lia` was trying to prove the lower bound from the monotonicity upper-bound lemma. I swapped the bullets: the first uses `Z.quot_pos` after rewriting with `sum_to_n_triangular_step`; the second uses `sum_to_n_triangular_mono` plus the precondition upper bound.

The direct `apply Z.quot_pos` still did not match because the actual goal is:

```coq
-2147483648 <= i * (i + 1) ÷ 2
```

while `Z.quot_pos` proves `0 <= ...`. I changed the first bullet to assert nonnegativity of the quotient and then close the signed lower bound by `lia`.

## 2026-04-23 05:09 +0800 - Add successor bound helper for `++i`

After `safety_wit_3` compiled, `proof_of_sum_to_n_safety_wit_4` failed with an incomplete proof. The proof state after `pre_process; entailer!` was:

```coq
n_pre, ret, i : Z
H : 1 <= i
H0 : i <= n_pre
H8 : 0 <= n_pre
H10 : n_pre * (n_pre + 1) ÷ 2 <= 2147483647
============================
i + 1 <= 2147483647
```

The loop body condition gives `1 <= i <= n_pre`, so it is enough to prove `n_pre + 1 <= INT_MAX`. This is not immediate linear arithmetic from the triangular bound because of `÷ 2`. I added:

```coq
Lemma sum_to_n_succ_bound_from_tri :
  forall n, 1 <= n ->
    n * (n + 1) ÷ 2 <= INT_MAX ->
    n + 1 <= INT_MAX.
```

The proof splits `n = 1`, where `2 <= INT_MAX` is direct, from `2 <= n`, where `Z.quot_le_lower_bound` proves `n + 1 <= n * (n + 1) ÷ 2`; the precondition bound then gives the result. The witness proof asserts `n_pre + 1 <= INT_MAX` with this helper and closes both increment bounds by `lia`.

The following compile showed that after this upper-bound bullet, there was no second goal:

```text
Error: [Focus] Wrong bullet -: No more goals.
```

So `entailer!` had already solved the lower-bound side condition for `i + 1`; I removed the redundant second `- lia` bullet and kept only the upper-bound proof.

The next compile reached `proof_of_sum_to_n_entail_wit_1` and failed with:

```text
Error: No such goal.
```

The proof was:

```coq
Proof.
  pre_process.
  entailer!.
Qed.
```

Here `pre_process` alone proves the invariant initialization witness, including `1 <= 1`, `1 <= n_pre + 1`, and `0 = ((1 - 1) * 1) ÷ 2`; the later `entailer!` ran after all goals were closed. I removed it.

## 2026-04-23 05:11 +0800 - Normalize quotient equality in preservation after `++i`

`proof_of_sum_to_n_entail_wit_4` failed after `pre_process; entailer!` with the remaining pure equality:

```coq
i * (i + 1) ÷ 2 = (i + 1 - 1) * (i + 1) ÷ 2
```

This is not a new arithmetic-series fact; it is only syntactic normalization of the next loop-head invariant after the `++i` step. I added:

```coq
replace (i + 1 - 1) with i by lia.
reflexivity.
```

This keeps the witness proof local and avoids introducing another helper for a one-step arithmetic simplification.

## 2026-04-23 05:12 +0800 - Normalize return-cell value in loop-exit witness

`proof_of_sum_to_n_entail_wit_5` is the bridge from loop exit to the explicit post-loop assertion. After `assert (i = n_pre + 1)` and `subst i`, `entailer!` reduced the goal to a heap-cell mismatch:

```coq
H2 : ret = (n_pre + 1 - 1) * (n_pre + 1) ÷ 2
============================
&( "ret") # Int |-> ret |-- &( "ret") # Int |-> (n_pre * (n_pre + 1) ÷ 2)
```

The missing step is the same syntactic normalization as the previous witness, but in a hypothesis rather than the goal. I inserted:

```coq
replace (n_pre + 1 - 1) with n_pre in H2 by lia.
subst ret.
entailer!.
```

This aligns the local `ret` resource with the loop-exit assertion value before the separation-logic entailment.

`entailer!` then left the pure copy of the same equality:

```coq
n_pre * (n_pre + 1) ÷ 2 =
  (n_pre + 1 - 1) * (n_pre + 1) ÷ 2
```

I added the same normalization after `entailer!`:

```coq
replace (n_pre + 1 - 1) with n_pre by lia.
reflexivity.
```
