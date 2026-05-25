## Manual witnesses after first successful `symexec`

Fresh `symexec` on `annotated/verify_20260423_052427_two_sum_sorted.c` succeeded and generated:

```text
two_sum_sorted_goal.v
two_sum_sorted_proof_auto.v
two_sum_sorted_proof_manual.v
two_sum_sorted_goal_check.v
```

The manual file contains exactly three admitted obligations:

```coq
Lemma proof_of_two_sum_sorted_safety_wit_4 : two_sum_sorted_safety_wit_4.
Proof. Admitted.

Lemma proof_of_two_sum_sorted_entail_wit_1 : two_sum_sorted_entail_wit_1.
Proof. Admitted.

Lemma proof_of_two_sum_sorted_return_wit_2 : two_sum_sorted_return_wit_2.
Proof. Admitted.
```

`two_sum_sorted_safety_wit_4` is the safety check for `a[left] + a[right]` inside the loop. The left side includes `left < right`, `0 <= left`, `right < n_pre`, and the precondition's pair-sum range:

```coq
forall i j,
  0 <= i /\ i < j /\ j < n_pre ->
    INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX
```

So the proof should reduce to applying that hypothesis with `i = left` and `j = right`, after `entailer!` exposes the pure context.

`two_sum_sorted_entail_wit_1` is invariant initialization. All target facts are copied directly from the precondition except the initial bounds and eliminated-pair facts for `left = 0` and `right = n_pre - 1`; those eliminated regions are empty and should be solved by arithmetic contradiction.

`two_sum_sorted_return_wit_2` is the final `return 0` postcondition. The target is an assertion-level disjunction:

```coq
([| 0 = 0 |] && [| forall i j, ... -> sum <> target_pre |] && IntArray.full ...)
||
(EX j i, [| 0 = 1 |] && ...)
```

The proof should use `Left`, preserve the `IntArray.full` resource, and prove the universal no-pair fact by splitting on whether `i < left`. If `i < left`, use the left-eliminated invariant. Otherwise, with `left >= right`, `left <= right + 1`, and `i < j`, arithmetic gives `right < j`, so the right-eliminated invariant applies.

I will first try conservative scripts using `pre_process`, `entailer!`, explicit `assert`s for the semantic cases, and `lia` for arithmetic side conditions.

## First compile failure: generated hypothesis numbers are unstable

The first compile replay reached `two_sum_sorted_proof_manual.v` and failed in `proof_of_two_sum_sorted_safety_wit_4`:

```text
File ".../two_sum_sorted_proof_manual.v", line 25, characters 16-23:
Error: Illegal application (Non-functional construction):
The expression "H2" of type "Zlength l = n_pre"
cannot be applied to the term "left" : "Z"
```

The proof script assumed that the pair-sum range hypothesis would be named `H2`, but after `pre_process`/`entailer!`, `H2` is the length equation. The fix is not semantic; it is proof-script robustness. I will replace numbered hypothesis references with `match goal` patterns that find the quantified range invariant or eliminated-pair invariant by shape, then instantiate it explicitly with the current indices.

## Second compile failure: `entail_wit_1` solved before `entailer!`

After making the safety proof robust, the next compile failed at `proof_of_two_sum_sorted_entail_wit_1`:

```text
File ".../two_sum_sorted_proof_manual.v", line 40, characters 2-12:
Error: No such goal.
```

This means `pre_process` fully solved the invariant-initialization witness, including the empty eliminated regions. I will remove the redundant `entailer!` from that lemma.

## Return witness proof-state inspection

The next failure was:

```text
File ".../two_sum_sorted_proof_manual.v", line 50, characters 4-204:
Error: No matching clauses for match.
```

I opened `two_sum_sorted_return_wit_2` in `coqtop` and stopped after:

```coq
pre_process.
Left.
entailer!.
intros i j Hij.
destruct Hij as [[Hi0 Hij] Hjn].
destruct (Z_lt_ge_dec i left) as [Hileft | Hlefti].
Show.
```

The relevant hypotheses are:

```coq
H10 :
  forall i_7 j_7 : Z,
  (0 <= i_7 < left /\ i_7 < j_7) /\ j_7 < n_pre ->
  Znth i_7 l 0 + Znth j_7 l 0 <> target_pre
H11 :
  forall i_8 j_8 : Z,
  (0 <= i_8 < j_8 /\ j_8 < n_pre) /\ right < j_8 ->
  Znth i_8 l 0 + Znth j_8 l 0 <> target_pre
```

The previous `match goal` pattern was too strict because the generated hypotheses use chained inequality notation and grouped conjunctions. I will use these concrete generated hypothesis names in this witness: the first branch applies `H10 i j`, and the second branch applies `H11 i j`; all required premises are arithmetic from `left >= right`, `left <= right + 1`, and `i < j`.

## Manual proof completed

After replacing the return witness branches with direct applications of the generated eliminated-region hypotheses, the full compile replay succeeded:

```text
compiled=two_sum_sorted_goal.v
compiled=two_sum_sorted_proof_auto.v
compiled=two_sum_sorted_proof_manual.v
compiled=two_sum_sorted_goal_check.v
```

The final manual proof file contains no `Admitted.` and no local `Axiom` declarations. The three manual witnesses are discharged as follows:

```coq
proof_of_two_sum_sorted_safety_wit_4
```

uses the pair-sum range invariant at `(left, right)` after `entailer!`.

```coq
proof_of_two_sum_sorted_entail_wit_1
```

is solved by `pre_process`, because the initial eliminated regions are empty.

```coq
proof_of_two_sum_sorted_return_wit_2
```

chooses the `return 0` side with `Left`, then proves the universal no-pair property by case splitting on `i < left`; the left case uses `H10`, and the right case uses `H11`.
