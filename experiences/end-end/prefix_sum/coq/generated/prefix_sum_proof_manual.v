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
From SimpleC.EE.CAV.verify_20260422_210632_prefix_sum Require Import prefix_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

Lemma prefix_sum_sum_sublist_snoc :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sum (sublist 0 (i + 1) l) =
      sum (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof (Zlength_correct l); lia).
  rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
  rewrite sum_app.
  simpl.
  lia.
Qed.

Local Open Scope sac.

Lemma proof_of_prefix_sum_safety_wit_3 : prefix_sum_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - subst acc.
    rewrite <- (prefix_sum_sum_sublist_snoc la i) by lia.
    match goal with
    | H : forall k : Z, _ |- _ =>
        pose proof (H (i + 1) ltac:(lia)) as Hrange
    end.
    lia.
  - subst acc.
    rewrite <- (prefix_sum_sum_sublist_snoc la i) by lia.
    match goal with
    | H : forall k : Z, _ |- _ =>
        pose proof (H (i + 1) ltac:(lia)) as Hrange
    end.
    lia.
Qed. 

Lemma proof_of_prefix_sum_entail_wit_1 : prefix_sum_entail_wit_1.
Proof.
  pre_process.
  Exists lo.
  Exists (@nil Z).
  entailer!.
Qed. 

Lemma proof_of_prefix_sum_entail_wit_2 : prefix_sum_entail_wit_2.
Proof.
  pre_process.
  assert (l2_2 = sublist i n_pre lo) as Hl2.
  {
    apply (proj2 (list_eq_ext 0 l2_2 (sublist i n_pre lo))).
    split.
    - rewrite Zlength_sublist by lia.
      lia.
    - intros t Ht.
      rewrite (Znth_sublist i t n_pre lo 0) by lia.
      assert (0 <= t < n_pre - i) as Hrange.
      {
        rewrite <- H6.
        exact Ht.
      }
      pose proof (H8 t Hrange) as Hsuffix.
      replace (t + i) with (i + t) by lia.
      exact Hsuffix.
  }
  subst l2_2.
  Exists (sublist (i + 1) n_pre lo).
  Exists (l1_2 ++ cons (sum (sublist 0 (i + 1) la)) nil).
  subst acc.
  rewrite <- (prefix_sum_sum_sublist_snoc la i) by lia.
  rewrite replace_Znth_app_r by lia.
  rewrite H5.
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
  assert (replace_Znth i (sum (sublist 0 (i + 1) la)) l1_2 = l1_2) as Hprefix_keep.
  {
    unfold replace_Znth.
    rewrite Zlength_correct in H5.
    replace (Z.to_nat i) with (length l1_2) by lia.
    apply Hreplace_nth_len.
  }
  assert (
    replace_Znth 0 (sum (sublist 0 (i + 1) la))
      (Znth i lo 0 :: sublist (i + 1) n_pre lo) =
    sum (sublist 0 (i + 1) la) :: sublist (i + 1) n_pre lo
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
  - intros t Ht.
    rewrite (Znth_sublist (i + 1) t n_pre lo 0) by lia.
    replace (t + (i + 1)) with (i + 1 + t) by lia.
    reflexivity.
  - intros t Ht.
    assert (t < i \/ t = i) as Hcase by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite H5; lia).
      apply H7.
      lia.
    + subst t.
      rewrite app_Znth2 by (rewrite H5; lia).
      rewrite H5.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in H5.
    rewrite Nat2Z.inj_add.
    rewrite H5.
    lia.
Qed. 

Lemma proof_of_prefix_sum_return_wit_1 : prefix_sum_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i_2 = n_pre) by lia.
  subst i_2.
  Exists (app l1 l2).
  entailer!.
  - intros i Hi_range.
    rewrite app_Znth1 by lia.
    apply H7; lia.
  - rewrite Zlength_app.
    lia.
Qed. 
