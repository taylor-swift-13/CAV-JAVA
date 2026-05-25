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
From SimpleC.EE.CAV.verify_20260422_151230_count_equal_to_k Require Import count_equal_to_k_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_equal_to_k.
Local Open Scope sac.

Lemma count_equal_to_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    count_equal_to_k_spec (l ++ x :: nil) k =
    count_equal_to_k_spec l k + (if Z.eq_dec x k then 1 else 0).
Proof.
  induction l; intros x k.
  - simpl. destruct (Z.eq_dec x k); lia.
  - simpl.
    destruct (Z.eq_dec a k);
      rewrite IHl;
      destruct (Z.eq_dec x k);
      lia.
Qed.

Lemma count_equal_to_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= count_equal_to_k_spec l k <= Zlength l.
Proof.
  induction l; intros k.
  - simpl. rewrite Zlength_nil. lia.
  - simpl. destruct (Z.eq_dec a k).
    + rewrite Zlength_cons. specialize (IHl k). destruct IHl. lia.
    + rewrite Zlength_cons. specialize (IHl k). destruct IHl. lia.
Qed.

Lemma proof_of_count_equal_to_k_safety_wit_3 : count_equal_to_k_safety_wit_3.
Proof.
  unfold count_equal_to_k_safety_wit_3.
  pre_process.
  prop_apply (store_int_range (&("n")) n_pre).
  Intros.
  change Int.min_signed with (-2147483648) in H6.
  change Int.max_signed with 2147483647 in H6.
  assert (0 <= ret <= i).
  {
    subst ret.
    pose proof (count_equal_to_k_spec_bounds (sublist 0 i l) k_pre) as Hbounds.
    rewrite Zlength_sublist in Hbounds by lia.
    replace (i - 0) with i in Hbounds by lia.
    exact Hbounds.
  }
  entailer!.
Qed. 

Lemma proof_of_count_equal_to_k_entail_wit_1 : count_equal_to_k_entail_wit_1.
Proof.
  unfold count_equal_to_k_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_count_equal_to_k_entail_wit_2_1 : count_equal_to_k_entail_wit_2_1.
Proof.
  unfold count_equal_to_k_entail_wit_2_1.
  intros.
  entailer!.
  subst ret.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite count_equal_to_k_spec_app_single.
  destruct (Z.eq_dec (Znth i l 0) k_pre); lia.
Qed. 

Lemma proof_of_count_equal_to_k_entail_wit_2_2 : count_equal_to_k_entail_wit_2_2.
Proof.
  unfold count_equal_to_k_entail_wit_2_2.
  intros.
  entailer!.
  subst ret.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite count_equal_to_k_spec_app_single.
  destruct (Z.eq_dec (Znth i l 0) k_pre); lia.
Qed. 

Lemma proof_of_count_equal_to_k_entail_wit_3 : count_equal_to_k_entail_wit_3.
Proof.
  unfold count_equal_to_k_entail_wit_3.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H4.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 
