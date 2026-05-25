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
From SimpleC.EE.CAV.verify_20260422_085356_array_sum_even_indices Require Import array_sum_even_indices_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_sum_even_indices.
Local Open Scope sac.

Lemma array_sum_even_indices_spec_app_single_even :
  forall (l : list Z) (x : Z),
    Zlength l mod 2 = 0 ->
    array_sum_even_indices_spec (l ++ x :: nil) =
    array_sum_even_indices_spec l + x.
Proof.
  fix IH 1.
  intros l x Hmod.
  destruct l.
  - simpl. lia.
  - destruct l.
    + rewrite Zlength_cons in Hmod.
      rewrite Zlength_nil in Hmod.
      cbv in Hmod.
      discriminate.
    + simpl.
      rewrite IH.
      * lia.
      * rewrite Zlength_cons in Hmod.
        rewrite Zlength_cons in Hmod.
        replace (Z.succ (Z.succ (Zlength l))) with (Zlength l + 2) in Hmod by lia.
        replace (Zlength l + 2) with (Zlength l + 1 * 2) in Hmod by lia.
        rewrite Z.mod_add in Hmod by lia.
        exact Hmod.
Qed.

Lemma array_sum_even_indices_spec_app_single_odd :
  forall (l : list Z) (x : Z),
    Zlength l mod 2 <> 0 ->
    array_sum_even_indices_spec (l ++ x :: nil) =
    array_sum_even_indices_spec l.
Proof.
  fix IH 1.
  intros l x Hmod.
  destruct l.
  - rewrite Zlength_nil in Hmod.
    cbv in Hmod.
    contradiction Hmod.
    reflexivity.
  - destruct l.
    + simpl. lia.
    + simpl.
      rewrite IH.
      * reflexivity.
      * intro Htail.
        apply Hmod.
        rewrite Zlength_cons.
        rewrite Zlength_cons.
        replace (Z.succ (Z.succ (Zlength l))) with (Zlength l + 2) by lia.
        replace (Zlength l + 2) with (Zlength l + 1 * 2) by lia.
        rewrite Z.mod_add by lia.
        exact Htail.
Qed.

Lemma array_sum_even_indices_spec_sublist_snoc_even :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    i mod 2 = 0 ->
    array_sum_even_indices_spec (sublist 0 (i + 1) l) =
    array_sum_even_indices_spec (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi Hmod.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite array_sum_even_indices_spec_app_single_even.
  - reflexivity.
  - rewrite Zlength_sublist by lia.
    replace (i - 0) with i by lia.
    exact Hmod.
Qed.

Lemma array_sum_even_indices_spec_sublist_snoc_odd :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    i mod 2 <> 0 ->
    array_sum_even_indices_spec (sublist 0 (i + 1) l) =
    array_sum_even_indices_spec (sublist 0 i l).
Proof.
  intros l i Hi Hmod.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite array_sum_even_indices_spec_app_single_odd.
  - reflexivity.
  - rewrite Zlength_sublist by lia.
    replace (i - 0) with i by lia.
    exact Hmod.
Qed.

Lemma proof_of_array_sum_even_indices_safety_wit_6 : array_sum_even_indices_safety_wit_6.
Proof.
  unfold array_sum_even_indices_safety_wit_6.
  intros.
  entailer!.
  - subst sum.
    assert (Hmod : i mod 2 = 0).
    { rewrite <- (Z.rem_mod_nonneg i 2) by lia. exact H. }
    specialize (H8 (i + 1)).
    assert (Hrange : 0 <= i + 1 /\ i + 1 <= n_pre) by lia.
    specialize (H8 Hrange).
    destruct H8 as [Hlo Hhi].
    rewrite array_sum_even_indices_spec_sublist_snoc_even in Hlo.
    2: { rewrite H6; lia. }
    2: { exact Hmod. }
    exact Hlo.
  - subst sum.
    assert (Hmod : i mod 2 = 0).
    { rewrite <- (Z.rem_mod_nonneg i 2) by lia. exact H. }
    specialize (H8 (i + 1)).
    assert (Hrange : 0 <= i + 1 /\ i + 1 <= n_pre) by lia.
    specialize (H8 Hrange).
    destruct H8 as [Hlo Hhi].
    rewrite array_sum_even_indices_spec_sublist_snoc_even in Hhi.
    2: { rewrite H6; lia. }
    2: { exact Hmod. }
    exact Hhi.
Qed. 

Lemma proof_of_array_sum_even_indices_entail_wit_1 : array_sum_even_indices_entail_wit_1.
Proof.
  unfold array_sum_even_indices_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_array_sum_even_indices_entail_wit_2_1 : array_sum_even_indices_entail_wit_2_1.
Proof.
  unfold array_sum_even_indices_entail_wit_2_1.
  intros.
  entailer!.
  subst sum.
  assert (Hmod : i_2 mod 2 = 0).
  { rewrite <- (Z.rem_mod_nonneg i_2 2) by lia. exact H. }
  rewrite array_sum_even_indices_spec_sublist_snoc_even.
  2: { rewrite H6; lia. }
  2: { exact Hmod. }
  reflexivity.
Qed. 

Lemma proof_of_array_sum_even_indices_entail_wit_2_2 : array_sum_even_indices_entail_wit_2_2.
Proof.
  unfold array_sum_even_indices_entail_wit_2_2.
  intros.
  entailer!.
  subst sum.
  assert (Hmod : i_2 mod 2 <> 0).
  {
    intro Hmod_eq.
    apply H.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod_eq.
  }
  rewrite array_sum_even_indices_spec_sublist_snoc_odd.
  2: { rewrite H6; lia. }
  2: { exact Hmod. }
  reflexivity.
Qed. 

Lemma proof_of_array_sum_even_indices_entail_wit_3 : array_sum_even_indices_entail_wit_3.
Proof.
  unfold array_sum_even_indices_entail_wit_3.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H5.
  f_equal.
  apply sublist_self.
  reflexivity.
Qed. 
