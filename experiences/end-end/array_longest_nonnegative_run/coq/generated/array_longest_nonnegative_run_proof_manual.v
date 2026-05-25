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
From SimpleC.EE.CAV.verify_20260422_054629_array_longest_nonnegative_run Require Import array_longest_nonnegative_run_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_longest_nonnegative_run.
Local Open Scope sac.

Lemma sublist_head_cons_Z :
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

Lemma proof_of_array_longest_nonnegative_run_entail_wit_1 : array_longest_nonnegative_run_entail_wit_1.
Proof.
  unfold array_longest_nonnegative_run_entail_wit_1.
  intros.
  entailer!.
  unfold array_longest_nonnegative_run_spec.
  rewrite sublist_self by lia.
  reflexivity.
Qed.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_1 : array_longest_nonnegative_run_entail_wit_2_1.
Proof.
  unfold array_longest_nonnegative_run_entail_wit_2_1.
  intros.
  entailer!.
  match goal with
  | Hacc : array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
           array_longest_nonnegative_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      simpl in Hacc;
      destruct (Z_le_dec 0 (Znth i l 0)); try lia;
      replace (Z.max best (current + 1)) with (current + 1) in Hacc by lia;
      exact Hacc
  end.
Qed.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_2 : array_longest_nonnegative_run_entail_wit_2_2.
Proof.
  unfold array_longest_nonnegative_run_entail_wit_2_2.
  intros.
  entailer!.
  match goal with
  | Hacc : array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
           array_longest_nonnegative_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      simpl in Hacc;
      destruct (Z_le_dec 0 (Znth i l 0)); try lia;
      replace (Z.max best (current + 1)) with best in Hacc by lia;
      exact Hacc
  end.
Qed.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_3 : array_longest_nonnegative_run_entail_wit_2_3.
Proof.
  unfold array_longest_nonnegative_run_entail_wit_2_3.
  intros.
  entailer!.
  match goal with
  | Hacc : array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
           array_longest_nonnegative_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      simpl in Hacc;
      destruct (Z_le_dec 0 (Znth i l 0)); try lia;
      replace (Z.max best 0) with best in Hacc by lia;
      exact Hacc
  end.
Qed.

Lemma proof_of_array_longest_nonnegative_run_return_wit_1 : array_longest_nonnegative_run_return_wit_1.
Proof.
  unfold array_longest_nonnegative_run_return_wit_1.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  match goal with
  | Hacc : array_longest_nonnegative_run_acc current best (sublist n_pre n_pre l) =
           array_longest_nonnegative_run_spec l |- _ =>
      rewrite sublist_nil in Hacc by lia;
      simpl in Hacc;
      exact Hacc
  end.
Qed.
