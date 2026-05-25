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
From SimpleC.EE.CAV.verify_20260423_045417_string_trim_last_char Require Import string_trim_last_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma length_replace_nth :
  forall {A : Type} (n : nat) (x : A) (l : list A),
    length (replace_nth n x l) = length l.
Proof.
  intros A n x l.
  revert n.
  induction l; intros n; destruct n; simpl; auto.
Qed.

Lemma nth_replace_nth_same :
  forall {A : Type} (n : nat) (x d : A) (l : list A),
    (n < length l)%nat ->
    nth n (replace_nth n x l) d = x.
Proof.
  intros A n x d l.
  revert n.
  induction l; intros n Hlt; destruct n; simpl in *; auto; try lia.
  apply IHl.
  lia.
Qed.

Lemma nth_replace_nth_diff :
  forall {A : Type} (k n : nat) (x d : A) (l : list A),
    k <> n ->
    nth k (replace_nth n x l) d = nth k l d.
Proof.
  intros A k n x d l.
  revert k n.
  induction l; intros k n Hneq; destruct k, n; simpl; auto; try contradiction.
Qed.

Lemma string_trim_last_char_Zlength_replace_Znth :
  forall {A : Type} (i : Z) (x : A) (l : list A),
    Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A i x l.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  rewrite length_replace_nth.
  reflexivity.
Qed.

Lemma string_trim_last_char_Znth_replace_Znth_same :
  forall {A : Type} (i : Z) (x d : A) (l : list A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i x l) d = x.
Proof.
  intros A i x d l Hi.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_same.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma string_trim_last_char_Znth_replace_Znth_diff :
  forall {A : Type} (k i : Z) (x d : A) (l : list A),
    0 <= k < Zlength l ->
    0 <= i ->
    k <> i ->
    Znth k (replace_Znth i x l) d = Znth k l d.
Proof.
  intros A k i x d l Hk Hi Hneq.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_diff.
  lia.
Qed.

Lemma proof_of_string_trim_last_char_return_wit_1 : string_trim_last_char_return_wit_1.
Proof.
  pre_process.
  Left.
  Exists (l ++ 0 :: nil).
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_string_trim_last_char_return_wit_2 : string_trim_last_char_return_wit_2.
Proof.
  pre_process.
  Right.
  Exists (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)).
  entailer!.
  - rewrite string_trim_last_char_Znth_replace_Znth_diff.
    + rewrite app_Znth2.
      * replace (n_pre - Zlength l) with 0 by lia.
        rewrite Znth0_cons.
        reflexivity.
      * lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    + lia.
    + lia.
  - rewrite string_trim_last_char_Znth_replace_Znth_same.
    + reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - intros i Hi.
    rewrite string_trim_last_char_Znth_replace_Znth_diff.
    + rewrite app_Znth1; lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    + lia.
    + lia.
  - rewrite string_trim_last_char_Zlength_replace_Znth.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.
