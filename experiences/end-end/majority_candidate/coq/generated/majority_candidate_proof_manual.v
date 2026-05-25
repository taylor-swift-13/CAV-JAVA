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
From SimpleC.EE.CAV.verify_20260422_190218_majority_candidate Require Import majority_candidate_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import majority_candidate.
Local Open Scope sac.

Lemma majority_candidate_sublist_head :
  forall (l : list Z) i n,
    0 <= i < n ->
    n <= Zlength l ->
    sublist i n l = Znth i l 0 :: sublist (i + 1) n l.
Proof.
  intros l i n Hi Hn.
  rewrite (sublist_split i n (i + 1) l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  reflexivity.
Qed.

Lemma majority_candidate_spec_nonempty :
  forall (l : list Z) n,
    1 <= n ->
    Zlength l = n ->
    majority_candidate_acc (Znth 0 l 0) 1 (sublist 1 n l) =
    majority_candidate_spec l.
Proof.
  intros l n Hn Hlen.
  destruct l.
  - rewrite Zlength_nil in Hlen. lia.
  - rename z into x.
    rename l into xs.
    rewrite Znth0_cons.
    unfold majority_candidate_spec.
    replace n with (Zlength (x :: xs)) by lia.
    rewrite (sublist_cons2 1 (Zlength (x :: xs)) x xs).
    + rewrite Zlength_cons.
      replace (1 - 1) with 0 by lia.
      replace (Z.succ (Zlength xs) - 1) with (Zlength xs) by lia.
      rewrite (sublist_self xs (Zlength xs)) by reflexivity.
      reflexivity.
    + split.
      * lia.
      * pose proof Zlength_nonneg xs. rewrite Zlength_cons. lia.
    + lia.
Qed.

Lemma majority_candidate_acc_sublist_step :
  forall (l : list Z) i n candidate count,
    0 <= i < n ->
    n <= Zlength l ->
    majority_candidate_acc candidate count (sublist i n l) =
    if Z.eq_dec count 0 then
      majority_candidate_acc (Znth i l 0) 1 (sublist (i + 1) n l)
    else if Z.eq_dec (Znth i l 0) candidate then
      majority_candidate_acc candidate (count + 1) (sublist (i + 1) n l)
    else
      majority_candidate_acc candidate (count - 1) (sublist (i + 1) n l).
Proof.
  intros l i n candidate count Hi Hn.
  rewrite majority_candidate_sublist_head by assumption.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_majority_candidate_entail_wit_1 : majority_candidate_entail_wit_1.
Proof.
  unfold majority_candidate_entail_wit_1.
  pre_process.
  assert (Hspec :
    majority_candidate_acc (Znth 0 l 0) 1 (sublist 1 n_pre l) =
    majority_candidate_spec l).
  {
    apply majority_candidate_spec_nonempty; lia.
  }
  entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto.
Qed. 

Lemma proof_of_majority_candidate_entail_wit_2_1 : majority_candidate_entail_wit_2_1.
Proof.
  unfold majority_candidate_entail_wit_2_1.
  pre_process.
  assert (Hstep :
    majority_candidate_acc (Znth i l 0) 1
      (sublist (i + 1) n_pre l) =
    majority_candidate_spec l).
  {
    assert (Hacc :=
      majority_candidate_acc_sublist_step l i n_pre candidate count).
    rewrite Hacc in H5 by lia.
    destruct (Z.eq_dec count 0).
    - exact H5.
    - lia.
  }
  entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto.
Qed. 

Lemma proof_of_majority_candidate_entail_wit_2_2 : majority_candidate_entail_wit_2_2.
Proof.
  unfold majority_candidate_entail_wit_2_2.
  pre_process.
  assert (Hstep :
    majority_candidate_acc candidate (count + 1)
      (sublist (i + 1) n_pre l) =
    majority_candidate_spec l).
  {
    assert (Hacc :=
      majority_candidate_acc_sublist_step l i n_pre candidate count).
    rewrite Hacc in H6 by lia.
    destruct (Z.eq_dec count 0) as [Hcount0 | Hcount0].
    - lia.
    - destruct (Z.eq_dec (Znth i l 0) candidate) as [Heq | Hneq].
      + exact H6.
      + lia.
  }
  entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto.
Qed. 

Lemma proof_of_majority_candidate_entail_wit_2_3 : majority_candidate_entail_wit_2_3.
Proof.
  unfold majority_candidate_entail_wit_2_3.
  pre_process.
  assert (Hstep :
    majority_candidate_acc candidate (count - 1)
      (sublist (i + 1) n_pre l) =
    majority_candidate_spec l).
  {
    assert (Hacc :=
      majority_candidate_acc_sublist_step l i n_pre candidate count).
    rewrite Hacc in H6 by lia.
    destruct (Z.eq_dec count 0) as [Hcount0 | Hcount0].
    - lia.
    - destruct (Z.eq_dec (Znth i l 0) candidate) as [Heq | Hneq].
      + lia.
      + exact H6.
  }
  entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto.
Qed. 

Lemma proof_of_majority_candidate_entail_wit_3 : majority_candidate_entail_wit_3.
Proof.
  unfold majority_candidate_entail_wit_3.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  assert (Hret : candidate = majority_candidate_spec l).
  {
    replace (sublist n_pre n_pre l) with (@nil Z) in H4.
    - simpl in H4. exact H4.
    - symmetry. apply sublist_nil. lia.
  }
  entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto.
Qed. 
