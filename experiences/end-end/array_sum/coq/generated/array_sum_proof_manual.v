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
From SimpleC.EE.CAV.verify_20260422_084036_array_sum Require Import array_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

Lemma sum_bound_signed_10000 :
  forall (l : list Z),
    (forall i, 0 <= i < Zlength l ->
      -10000 <= Znth i l 0 <= 10000) ->
    -10000 * Zlength l <= sum l <= 10000 * Zlength l.
Proof.
  intros l Hrange.
  induction l.
  - rewrite Zlength_nil. unfold sum. simpl. lia.
  - change (sum (a :: l)) with (a + sum l).
    rewrite Zlength_cons.
    assert (Hx : -10000 <= a <= 10000).
    {
      rewrite <- (Znth0_cons a l 0).
      apply Hrange.
      split.
      - lia.
      - rewrite Zlength_cons.
        pose proof (Zlength_nonneg l).
        lia.
    }
    assert (Hxs : -10000 * Zlength l <= sum l <= 10000 * Zlength l).
    {
      apply IHl.
      intros i Hi.
      specialize (Hrange (i + 1)).
      simpl in Hrange.
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      split.
      - lia.
      - rewrite Zlength_cons. lia.
    }
    pose proof (Zlength_nonneg l).
    replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
    replace (-10000 * (Zlength l + 1)) with (-10000 * Zlength l - 10000) by lia.
    replace (10000 * (Zlength l + 1)) with (10000 * Zlength l + 10000) by lia.
    nia.
Qed.

Lemma sum_sublist_snoc :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sum (sublist 0 (i + 1) l) =
      sum (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof (Zlength_correct l); lia).
  rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
  rewrite sum_app.
    simpl. lia.
Qed.

Local Open Scope sac.

Lemma proof_of_array_sum_safety_wit_3 : array_sum_safety_wit_3.
Proof.
  unfold array_sum_safety_wit_3.
  pre_process.
  entailer!.
  - subst ret.
    rewrite <- (sum_sublist_snoc l i) by lia.
    assert (-10000 * Zlength (sublist 0 (i + 1) l) <=
            sum (sublist 0 (i + 1) l) <=
            10000 * Zlength (sublist 0 (i + 1) l)) as Hsum_bound.
    {
      apply sum_bound_signed_10000.
      intros k Hk.
      rewrite Znth_sublist0 by (rewrite Zlength_sublist in Hk by lia; lia).
      apply H6.
      rewrite Zlength_sublist in Hk by lia.
      lia.
    }
    rewrite Zlength_sublist in Hsum_bound by lia.
    change INT_MAX with 2147483647.
    lia.
  - subst ret.
    rewrite <- (sum_sublist_snoc l i) by lia.
    assert (-10000 * Zlength (sublist 0 (i + 1) l) <=
            sum (sublist 0 (i + 1) l) <=
            10000 * Zlength (sublist 0 (i + 1) l)) as Hsum_bound.
    {
      apply sum_bound_signed_10000.
      intros k Hk.
      rewrite Znth_sublist0 by (rewrite Zlength_sublist in Hk by lia; lia).
      apply H6.
      rewrite Zlength_sublist in Hk by lia.
      lia.
    }
    rewrite Zlength_sublist in Hsum_bound by lia.
    change INT_MIN with (-2147483648).
    lia.
Qed. 

Lemma proof_of_array_sum_entail_wit_1 : array_sum_entail_wit_1.
Proof.
  unfold array_sum_entail_wit_1.
  pre_process.
Qed. 

Lemma proof_of_array_sum_entail_wit_2 : array_sum_entail_wit_2.
Proof.
  unfold array_sum_entail_wit_2.
  pre_process.
  entailer!.
  subst ret.
  rewrite <- (sum_sublist_snoc l i_2) by lia.
  reflexivity.
Qed. 

Lemma proof_of_array_sum_entail_wit_3 : array_sum_entail_wit_3.
Proof.
  unfold array_sum_entail_wit_3.
  pre_process.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H5.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 
