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
From SimpleC.EE.CAV.verify_20260422_031957_array_count_greater_than_k Require Import array_count_greater_than_k_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_greater_than_k.
Local Open Scope sac.

Lemma array_count_greater_than_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    array_count_greater_than_k_spec (l ++ x :: nil) k =
    array_count_greater_than_k_spec l k + (if Z_gt_dec x k then 1 else 0).
Proof.
  induction l; intros x k.
  - simpl. destruct (Z_gt_dec x k); lia.
  - simpl.
    destruct (Z_gt_dec a k);
      rewrite IHl;
      destruct (Z_gt_dec x k);
      lia.
Qed.

Lemma array_count_greater_than_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= array_count_greater_than_k_spec l k <= Zlength l.
Proof.
  induction l; intros k.
  - simpl. rewrite Zlength_nil. lia.
  - simpl. destruct (Z_gt_dec a k).
    + rewrite Zlength_cons. specialize (IHl k). destruct IHl. lia.
    + rewrite Zlength_cons. specialize (IHl k). destruct IHl. lia.
Qed.

Lemma proof_of_array_count_greater_than_k_safety_wit_3 : array_count_greater_than_k_safety_wit_3.
Proof.
  unfold array_count_greater_than_k_safety_wit_3.
  pre_process.
  prop_apply (store_int_range (&("n")) n_pre).
  Intros.
  change Int.min_signed with (-2147483648) in H6.
  change Int.max_signed with 2147483647 in H6.
  assert (0 <= cnt <= i).
  {
    subst cnt.
    pose proof (array_count_greater_than_k_spec_bounds (sublist 0 i l) k_pre) as Hbounds.
    rewrite Zlength_sublist in Hbounds by lia.
    replace (i - 0) with i in Hbounds by lia.
    exact Hbounds.
  }
  entailer!.
Qed. 

Lemma proof_of_array_count_greater_than_k_entail_wit_1 : array_count_greater_than_k_entail_wit_1.
Proof.
  unfold array_count_greater_than_k_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_array_count_greater_than_k_entail_wit_2_1 : array_count_greater_than_k_entail_wit_2_1.
Proof.
  unfold array_count_greater_than_k_entail_wit_2_1.
  intros.
  entailer!.
  subst cnt.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite array_count_greater_than_k_spec_app_single.
  destruct (Z_gt_dec (Znth i l 0) k_pre); lia.
Qed. 

Lemma proof_of_array_count_greater_than_k_entail_wit_2_2 : array_count_greater_than_k_entail_wit_2_2.
Proof.
  unfold array_count_greater_than_k_entail_wit_2_2.
  intros.
  entailer!.
  subst cnt.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite array_count_greater_than_k_spec_app_single.
  destruct (Z_gt_dec (Znth i l 0) k_pre); lia.
Qed. 

Lemma proof_of_array_count_greater_than_k_entail_wit_3 : array_count_greater_than_k_entail_wit_3.
Proof.
  unfold array_count_greater_than_k_entail_wit_3.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H4.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 
