Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260422_014304_array_add Require Import array_add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_add_safety_wit_2 : array_add_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  - pose proof (H13 i ltac:(lia)) as Hsum.
    lia.
  - pose proof (H13 i ltac:(lia)) as Hsum.
    lia.
Qed.

Lemma proof_of_array_add_entail_wit_1 : array_add_entail_wit_1.
Proof.
  pre_process.
  Exists lo.
  Exists nil.
  entailer!.
Qed.

Lemma proof_of_array_add_entail_wit_2 : array_add_entail_wit_2.
Proof.
  pre_process.
  Exists (sublist (i_2 + 1) n_pre lo).
  Exists l1'.
  entailer!.
  - intros k Hk.
    rewrite Znth_sublist by lia.
    replace (k + (i_2 + 1)) with (i_2 + 1 + k) by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma proof_of_array_add_return_wit_1 : array_add_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i_3 = n_pre) by lia.
  subst i_3.
  Exists (app l1 l2).
  entailer!.
  - intros i Hi_range.
    rewrite app_Znth1 by lia.
    apply H7; lia.
  - rewrite Zlength_app.
    lia.
Qed.

Lemma proof_of_array_add_which_implies_wit_1 : array_add_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_split_to_missing_i a_pre i n_pre la 0); try lia.
  sep_apply (IntArray.full_split_to_missing_i b_pre i n_pre lb 0); try lia.
  sep_apply (IntArray.full_split_to_missing_i out_pre i n_pre (app l1 l2) 0); try lia.
  replace (Znth i (app l1 l2) 0) with (Znth i lo 0).
  entailer!.
  rewrite app_Znth2 by lia.
  replace (i - Zlength l1) with 0 by lia.
  rewrite H7 by lia.
  replace (i + 0) with i by lia.
  reflexivity.
Qed.

Lemma proof_of_array_add_which_implies_wit_2 : array_add_which_implies_wit_2.
Proof.
  pre_process.
  assert (l2 = sublist i n_pre lo) as Hl2.
  {
    apply (proj2 (list_eq_ext 0 l2 (sublist i n_pre lo))).
    split.
    - rewrite Zlength_sublist by lia.
      lia.
    - intros k Hk.
      rewrite (Znth_sublist i k n_pre lo 0) by lia.
      assert (0 <= k < n_pre - i) as Hrange.
      {
        rewrite <- H5.
        exact Hk.
      }
      pose proof (H7 k Hrange) as Hsuffix.
      replace (k + i) with (i + k) by lia.
      exact Hsuffix.
  }
  subst l2.
  Exists (l1 ++ cons (Znth i la 0 + Znth i lb 0) nil).
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  rewrite replace_Znth_Znth by tauto.
  rewrite replace_Znth_app_r by lia.
  rewrite H4.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i n_pre (i + 1) lo) by (pose proof (Zlength_correct lo); lia).
  rewrite (sublist_single i lo 0) by (pose proof (Zlength_correct lo); lia).
  simpl.
  assert (forall (l : list Z) (z : Z), replace_nth (length l) z l = l) as Hreplace_nth_len.
  {
    intros l z.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  assert (replace_Znth i (Znth i la 0 + Znth i lb 0) l1 = l1) as Hprefix_keep.
  {
    unfold replace_Znth.
    rewrite Zlength_correct in H4.
    replace (Z.to_nat i) with (length l1) by lia.
    apply Hreplace_nth_len.
  }
  assert (
    replace_Znth 0 (Znth i la 0 + Znth i lb 0)
      (Znth i lo 0 :: sublist (i + 1) n_pre lo) =
    Znth i la 0 + Znth i lb 0 :: sublist (i + 1) n_pre lo
  ) as Hhead_write.
  {
    reflexivity.
  }
  simpl.
  rewrite Hprefix_keep.
  rewrite Hhead_write.
  rewrite <- app_assoc.
  simpl.
  entailer!.
  - intros k Hk.
    assert (k < i \/ k = i) as Hcase by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite H4; lia).
      apply H6.
      lia.
    + subst k.
      rewrite app_Znth2 by (rewrite H4; lia).
      rewrite H4.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in H4.
    rewrite Nat2Z.inj_add.
    rewrite H4.
    lia.
Qed.
