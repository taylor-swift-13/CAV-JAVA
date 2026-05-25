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
From SimpleC.EE.CAV.verify_20260422_184334_longest_increasing_run Require Import longest_increasing_run_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import longest_increasing_run.
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

Lemma longest_increasing_run_spec_nonempty_acc :
  forall (l : list Z) n,
    n <> 0 ->
    0 <= n ->
    Zlength l = n ->
    longest_increasing_run_acc (Znth (1 - 1) l 0) 1 1 (sublist 1 n l) =
      longest_increasing_run_spec l.
Proof.
  intros l n Hnz Hn Hlen.
  destruct l.
  - rewrite Zlength_nil in Hlen. lia.
  - simpl.
    replace (1 - 1) with 0 by lia.
    simpl.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons in *; lia).
    rewrite sublist_self by (rewrite Zlength_cons in Hlen; lia).
    reflexivity.
Qed.

Lemma longest_increasing_run_acc_step :
  forall prev cur best x xs,
    longest_increasing_run_acc prev cur best (x :: xs) =
      if Z_lt_dec prev x then
        longest_increasing_run_acc x (cur + 1) (Z.max best (cur + 1)) xs
      else
        longest_increasing_run_acc x 1 best xs.
Proof.
  intros.
  simpl.
  destruct (Z_lt_dec prev x); reflexivity.
Qed.

Lemma proof_of_longest_increasing_run_entail_wit_1 : longest_increasing_run_entail_wit_1.
Proof.
  unfold longest_increasing_run_entail_wit_1.
  intros.
  entailer!.
  apply longest_increasing_run_spec_nonempty_acc; lia.
Qed. 

Lemma proof_of_longest_increasing_run_entail_wit_2_1 : longest_increasing_run_entail_wit_2_1.
Proof.
  unfold longest_increasing_run_entail_wit_2_1.
  intros.
  entailer!.
  match goal with
  | Hacc : longest_increasing_run_acc (Znth (i - 1) l 0) cur best
             (sublist i n_pre l) = longest_increasing_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      rewrite longest_increasing_run_acc_step in Hacc;
      destruct (Z_lt_dec (Znth (i - 1) l 0) (Znth i l 0)); try lia;
      replace (Z.max best (cur + 1)) with (cur + 1) in Hacc by lia;
      replace (i + 1 - 1) with i by lia;
      exact Hacc
  end.
Qed. 

Lemma proof_of_longest_increasing_run_entail_wit_2_2 : longest_increasing_run_entail_wit_2_2.
Proof.
  unfold longest_increasing_run_entail_wit_2_2.
  intros.
  entailer!.
  match goal with
  | Hacc : longest_increasing_run_acc (Znth (i - 1) l 0) cur best
             (sublist i n_pre l) = longest_increasing_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      rewrite longest_increasing_run_acc_step in Hacc;
      destruct (Z_lt_dec (Znth (i - 1) l 0) (Znth i l 0)); try lia;
      replace (i + 1 - 1) with i by lia;
      exact Hacc
  end.
Qed. 

Lemma proof_of_longest_increasing_run_entail_wit_2_3 : longest_increasing_run_entail_wit_2_3.
Proof.
  unfold longest_increasing_run_entail_wit_2_3.
  intros.
  entailer!.
  match goal with
  | Hacc : longest_increasing_run_acc (Znth (i - 1) l 0) cur best
             (sublist i n_pre l) = longest_increasing_run_spec l |- _ =>
      rewrite sublist_head_cons_Z in Hacc by lia;
      rewrite longest_increasing_run_acc_step in Hacc;
      destruct (Z_lt_dec (Znth (i - 1) l 0) (Znth i l 0)); try lia;
      replace (Z.max best (cur + 1)) with best in Hacc by lia;
      replace (i + 1 - 1) with i by lia;
      exact Hacc
  end.
Qed. 

Lemma proof_of_longest_increasing_run_return_wit_1 : longest_increasing_run_return_wit_1.
Proof.
  unfold longest_increasing_run_return_wit_1.
  intros.
  entailer!.
  match goal with
  | Hn : n_pre = 0, Hlen : Zlength l = n_pre |- _ =>
      rewrite Hn in Hlen;
      apply Zlength_nil_inv in Hlen;
      subst l;
      reflexivity
  end.
Qed. 

Lemma proof_of_longest_increasing_run_return_wit_2 : longest_increasing_run_return_wit_2.
Proof.
  unfold longest_increasing_run_return_wit_2.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  match goal with
  | Hacc : longest_increasing_run_acc (Znth (n_pre - 1) l 0) cur best
             (sublist n_pre n_pre l) = longest_increasing_run_spec l |- _ =>
      rewrite sublist_nil in Hacc by lia;
      simpl in Hacc;
      exact Hacc
  end.
Qed. 
