## 2026-04-22 13:03 +0800 - Manual obligations after successful symexec

Fresh `symexec` succeeded for `annotated/verify_20260422_130100_bubble_sort.c` and generated:

```text
coq/generated/bubble_sort_goal.v
coq/generated/bubble_sort_proof_auto.v
coq/generated/bubble_sort_proof_manual.v
coq/generated/bubble_sort_goal_check.v
```

The generated manual file currently contains five admitted lemmas:

```coq
Lemma proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Lemma proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Lemma proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Lemma proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Lemma proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
```

`bubble_sort_entail_wit_1` is outer invariant initialization. The witness should be `lc = l`; `Permutation l l` is `Permutation_refl`, both sorted-suffix/cross-boundary implications are vacuous because `n_pre - 0 = n_pre`, and the heap is the original `IntArray.full`.

`bubble_sort_entail_wit_2` is inner invariant initialization at `j = 0`. The witness should be the current outer list `lc`; the local maximum fact over `0 <= p < 0` is vacuous, and `0 + 1 <= n_pre - i` follows from `i < n_pre`.

`bubble_sort_entail_wit_3_1` is the swap branch after:

```c
int t = a[j];
a[j] = a[j + 1];
a[j + 1] = t;
```

The heap list is:

```coq
replace_Znth (j + 1) (Znth j lc_3 0)
  (replace_Znth j (Znth (j + 1) lc_3 0) lc_3)
```

This proof needs local helper lemmas for `replace_Znth` length, point lookup at the replaced index, point lookup away from the replaced index, adjacent-swap permutation, and preservation of the suffix/cross-order/local-maximum facts under a swap strictly before `n_pre - i_2`. The reusable pattern comes from the archived `selection_sort` proof, whose helpers prove the same `replace_Znth` and `Permutation` facts for array swaps.

`bubble_sort_entail_wit_4` is outer invariant preservation after the inner loop exits. From `j + 1 >= n_pre - i` and `j + 1 <= n_pre - i`, we get `j = n_pre - i - 1`. The inner local maximum fact gives all old-prefix elements `<= lc_3[j]`; the old cross-boundary fact gives `lc_3[j] <=` every element in the old suffix `[n_pre - i, n_pre)`. Together they establish the new suffix and cross-boundary properties for `i + 1`.

`bubble_sort_return_wit_1` is final postcondition. From `i_2 >= n_pre` and `i_2 <= n_pre`, `i_2 = n_pre`; choosing `l0 = lc` makes the outer suffix sortedness fact cover the whole array because `n_pre - i_2 = 0`.

Planned edit: add local helper lemmas to `coq/generated/bubble_sort_proof_manual.v`, then replace the five admitted bodies with explicit `Exists` choices, `Intros`, `prop_apply IntArray.full_length`, and helper calls. No `Axiom` will be added.

## 2026-04-22 13:04 +0800 - First compile failure in local replace_nth helper

The first compile replay reached `coq/generated/bubble_sort_proof_manual.v` and failed before any generated witness body:

```text
File ".../bubble_sort_proof_manual.v", line 54, characters 4-14:
Error: Not an inductive definition.
```

The failing helper fragment was:

```coq
Lemma bubble_sort_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros T l.
  induction l; intros.
  - destruct a; destruct b; try lia; reflexivity.
  - destruct a; destruct b; simpl; try reflexivity; try lia.
    apply IHl; lia.
Qed.
```

After `induction l`, the list head binder shadowed the index name `a`, so `destruct a` in the cons case was destructing the element rather than the natural index. The fix is to name the induction binders explicitly and use `idx` / `repl` for the two natural indices:

```coq
induction l as [|h t IH]; intros idx repl v u Hneq.
- destruct idx; destruct repl; try lia; reflexivity.
- destruct idx; destruct repl; simpl; try reflexivity; try lia.
  apply IH; lia.
```

This keeps the helper structurally identical but removes the shadowing that caused the non-inductive destruct error. Next step is to rerun the same full compile command.

## 2026-04-22 13:15 +0800 - Manual proof completed and goal_check passed

After the helper-shadowing fix, the remaining proof work was concentrated in the adjacent-swap helper and two generated witnesses.

For `bubble_sort_adjacent_swap_perm`, the first split proof failed because the tail after splitting `skipn (S (Z.to_nat j)) l` was not convertible to the earlier `tail := skipn (S (S (Z.to_nat j))) l`. I fixed the helper by setting `tail` after the second `list_split_nth`:

```coq
rewrite (list_split_nth _ 0 (skipn (S (Z.to_nat j)) l) 0 Hj1_nat).
set (x0 := nth (Z.to_nat j) l 0).
set (y0 := nth 0 (skipn (S (Z.to_nat j)) l) 0).
set (tail := skipn (S 0) (skipn (S (Z.to_nat j)) l)).
```

For `proof_of_bubble_sort_entail_wit_3_1`, `entailer!` left the permutation goal after the quantified-order goals. I used the generated hypothesis `H7 : Permutation l lc_3` and the local adjacent-swap permutation lemma:

```coq
eapply Permutation_trans.
- exact H7.
- apply bubble_sort_adjacent_swap_perm. lia.
```

For `proof_of_bubble_sort_entail_wit_4`, the first remaining goal was a separation entailment for removing the local `j` variable, not a quantified pure goal:

```coq
&( "j") # Int |-> j |-- &( "j") # Int |->_
```

The correct proof step was:

```coq
sep_apply store_int_undef_store_int.
entailer!.
```

Then the two pure quantified goals were discharged by `bubble_sort_outer_cross_extend` and `bubble_sort_outer_suffix_extend`, using the inner-loop exit facts `j + 1 >= n_pre - i` and `j + 1 <= n_pre - i` to identify the newly prepended suffix element.

For `proof_of_bubble_sort_return_wit_1`, the last compile failure was caused by applying the length hypothesis `H3 : Zlength lc = n_pre` where the sortedness hypothesis was needed. The final proof uses:

```coq
replace i_2 with n_pre in H5 by lia.
apply H5; lia.
```

Final replay command compiled, in order:

```text
bubble_sort_goal.v
bubble_sort_proof_auto.v
bubble_sort_proof_manual.v
bubble_sort_goal_check.v
```

`bubble_sort_proof_manual.v` now contains no `Admitted.` and no added `Axiom`. The generated `proof_auto.v` still contains tool-generated admitted auto lemmas, and `bubble_sort_goal.v` contains the tool-generated axiom declarations expected by the QCP `goal_check` inclusion model; these were recorded in the workspace fingerprint with controlled verification-status keywords.
