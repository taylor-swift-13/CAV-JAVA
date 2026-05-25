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
From SimpleC.EE.CAV.verify_20260422_153249_count_positive Require Import count_positive_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_positive.
Local Open Scope sac.

Lemma count_positive_spec_app_single :
  forall (l : list Z) (x : Z),
    count_positive_spec (l ++ x :: nil) =
    count_positive_spec l + (if Z_gt_dec x 0 then 1 else 0).
Proof.
  induction l; intros x.
  - simpl. destruct (Z_gt_dec x 0); lia.
  - simpl.
    destruct (Z_gt_dec a 0);
      rewrite IHl;
      destruct (Z_gt_dec x 0);
      lia.
Qed.

Lemma count_positive_spec_bounds :
  forall (l : list Z),
    0 <= count_positive_spec l <= Zlength l.
Proof.
  induction l.
  - simpl. rewrite Zlength_nil. lia.
  - simpl. destruct (Z_gt_dec a 0).
    + rewrite Zlength_cons. destruct IHl. lia.
    + rewrite Zlength_cons. destruct IHl. lia.
Qed.

Lemma proof_of_count_positive_safety_wit_4 : count_positive_safety_wit_4.
Proof.
  unfold count_positive_safety_wit_4.
  pre_process.
  prop_apply (store_int_range (&("n")) n_pre).
  Intros.
  change Int.min_signed with (-2147483648) in H6.
  change Int.max_signed with 2147483647 in H6.
  assert (0 <= cnt <= i).
  {
    subst cnt.
    pose proof (count_positive_spec_bounds (sublist 0 i l)) as Hbounds.
    rewrite Zlength_sublist in Hbounds by lia.
    replace (i - 0) with i in Hbounds by lia.
    exact Hbounds.
  }
  entailer!.
Qed. 

Lemma proof_of_count_positive_entail_wit_1 : count_positive_entail_wit_1.
Proof.
  unfold count_positive_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_count_positive_entail_wit_2_1 : count_positive_entail_wit_2_1.
Proof.
  unfold count_positive_entail_wit_2_1.
  intros.
  entailer!.
  subst cnt.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite count_positive_spec_app_single.
  destruct (Z_gt_dec (Znth i l 0) 0); lia.
Qed. 

Lemma proof_of_count_positive_entail_wit_2_2 : count_positive_entail_wit_2_2.
Proof.
  unfold count_positive_entail_wit_2_2.
  intros.
  entailer!.
  subst cnt.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite count_positive_spec_app_single.
  destruct (Z_gt_dec (Znth i l 0) 0); lia.
Qed. 

Lemma proof_of_count_positive_entail_wit_3 : count_positive_entail_wit_3.
Proof.
  unfold count_positive_entail_wit_3.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H4.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 
