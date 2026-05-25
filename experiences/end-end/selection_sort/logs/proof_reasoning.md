# Proof Reasoning

## Initial manual witness analysis

Fresh symexec succeeded on `annotated/verify_20260422_220436_selection_sort.c` and generated `selection_sort_goal.v`, `selection_sort_proof_auto.v`, `selection_sort_proof_manual.v`, and `selection_sort_goal_check.v`.

Manual obligations in `coq/generated/selection_sort_proof_manual.v`:

```coq
Lemma proof_of_selection_sort_entail_wit_1 : selection_sort_entail_wit_1.
Lemma proof_of_selection_sort_entail_wit_2 : selection_sort_entail_wit_2.
Lemma proof_of_selection_sort_entail_wit_4 : selection_sort_entail_wit_4.
Lemma proof_of_selection_sort_return_wit_1 : selection_sort_return_wit_1.
```

The first witness initializes the outer invariant by choosing `l_outer = l`; all pairwise order facts are vacuous because the prefix bound is `q < 0`, and `Permutation l l` is reflexive.

The second witness initializes the inner invariant by choosing `l_inner = l_outer`; the new minimum fact is `forall k, i <= k /\ k < i + 1 -> Znth i l_outer 0 <= Znth k l_outer 0`, which reduces to `k = i` and reflexivity.

The hard witness is `selection_sort_entail_wit_4`. Its left side contains the heap after the two assignments:

```coq
IntArray.full a_pre n_pre
  (replace_Znth min_idx (Znth i l_inner 0)
    (replace_Znth i (Znth min_idx l_inner 0) l_inner))
```

and the right side requires the next outer invariant at `i + 1`: length, permutation, pairwise sorted prefix, cross prefix-to-suffix order, and local variables `tmp`, `min_idx`, and `j` converted from valued stores to undef stores. The existing archived selection-sort proof gives reusable non-adjacent swap lemmas for `replace_Znth`, `Znth` at swapped/unchanged positions, length, and `Permutation`. This task differs because the contract uses pairwise sortedness instead of `sorted_z`; therefore the new proof needs pairwise helpers:

```coq
selection_sort_swap_pairwise_prefix
selection_sort_swap_cross_order
```

The return witness should choose `lr = l_outer`, derive `i_2 = n_pre` from loop exit and invariant bounds, and use the outer invariant's pairwise-prefix fact directly as the postcondition sortedness over the full array.

## First compile failure in pairwise prefix helper

The first compile replay passed `selection_sort_goal.v` and `selection_sort_proof_auto.v`, then failed in `selection_sort_proof_manual.v` at the helper `selection_sort_swap_pairwise_prefix`:

```text
File ".../selection_sort_proof_manual.v", line 306, characters 21-30:
Error:
Unable to unify "Znth min_idx l 0" with
 "Znth i (selection_sort_swap l i min_idx) 0".
```

The failing branch is the `q = i` and `p = i` case. The proof had rewritten the right-side `Znth i (selection_sort_swap ...)` to `Znth min_idx l 0`, but it then tried `Z.le_refl` while the left side was still `Znth i (selection_sort_swap ...)`. The fix is to explicitly rewrite the left side with `selection_sort_swap_Znth_i` after `subst p`; then the goal becomes `Znth min_idx l 0 <= Znth min_idx l 0`.

## Second compile failure in entail_wit_4 bullet order

After fixing the helper, compile again reached `proof_of_selection_sort_entail_wit_4` and failed at the first pure bullet after local-store cleanup:

```text
File ".../selection_sort_proof_manual.v", line 379, characters 11-28:
Error: Unable to unify "list ?M..." with "Z".
```

The context showed the expected swap hypotheses (`H6 : Zlength l_inner = n_pre`, `H7 : Permutation l l_inner`, `H8/H9` for pairwise order, `H10` for suffix minimum). The attempted bullet was `eapply Permutation_trans`, but the active subgoal was actually the length fact for the existential `l_outer`, not the permutation fact. I inserted an explicit length bullet before permutation:

```coq
unfold selection_sort_swap.
rewrite !selection_sort_replace_Znth_length.
exact H6.
```

This matches the generated right-side order: heap cleanup, length, permutation, pairwise prefix, and cross order.

The next compile attempt showed that the length goal had already been normalized by the earlier `unfold selection_sort_swap` before `entailer!`:

```text
Error: Found no subterm matching
"Zlength (replace_Znth ?M ?M ?M)" in the current goal.
```

The active length goal was simply the generated hypothesis `H6 : Zlength l_inner = n_pre`, so the length bullet was reduced to `exact H6`.

That interpretation was still too coarse. The following compile reported that the active subgoal at that bullet was actually the cross prefix-to-suffix order:

```text
expected type
"forall p_2 q_2 : Z,
  (0 <= p_2 < i + 1 /\ i + 1 <= q_2) /\ q_2 < n_pre -> ..."
```

So `entailer!` had already handled length and was asking first for the second quantified ordering fact. I moved the `selection_sort_swap_cross_order` proof into that first pure bullet, leaving permutation and pairwise-prefix bullets to follow.

The next compile failure was a range-conjunction shape mismatch:

```text
Hp' : 0 <= p' /\ p' < i /\ i <= q' < n_pre
expected: (0 <= p' < i /\ i <= q') /\ q' < n_pre
```

The helper lemmas use flatter conjunctions, while the generated invariant hypotheses use nested chained-comparison shapes. I changed the uses of `H8` and `H9` from `exact (H... Hp')` to `apply H...; lia`, so Coq rebuilds the generated range shape from the helper's range facts.

After cross-order closed, compile failed again at `eapply Permutation_trans` with the same "list vs Z" unification symptom. This means the next active goal was still an ordering goal, specifically the pairwise-prefix fact. I moved the permutation bullet after the pairwise-prefix helper call. The stable remaining order after local-store cleanup is therefore: cross order, pairwise prefix, permutation.

The pairwise-prefix helper then failed on the final range argument:

```text
Hpq : 0 <= p <= q /\ q < i + 1
expected: 0 <= p /\ p <= q < i + 1
```

This is another generated chained-comparison shape versus helper conjunction shape mismatch. The final helper side condition now uses `lia` instead of `exact Hpq`.

At `Qed`, Coq still reported an incomplete proof. Running the theorem through `coqtop` with `Show` revealed that the permutation bullet used `eapply Permutation_trans` without fixing the middle list, leaving an evar goal `Permutation l ?l'`, and after the swap permutation was solved there was still a length goal:

```coq
Zlength
  (replace_Znth min_idx (Znth i l_inner 0)
    (replace_Znth i (Znth min_idx l_inner 0) l_inner)) = n_pre
```

The fix is to set the permutation middle list explicitly:

```coq
eapply Permutation_trans with (l' := l_inner).
```

and then close the remaining length goal by rewriting both `replace_Znth` length-preservation lemmas and applying `H6 : Zlength l_inner = n_pre`.

After the swap witness compiled, the return witness failed because I used the old hypothesis number:

```text
Unable to unify "Permutation l l_outer" with
"Znth p l_outer 0 <= Znth q l_outer 0".
```

In the generated return witness, `H3` is `Permutation l l_outer` and `H4` is the pairwise prefix sortedness fact. The final proof now applies `H4` and uses `lia` to rewrite the exit condition `i_2 = n_pre` into the postcondition range.
