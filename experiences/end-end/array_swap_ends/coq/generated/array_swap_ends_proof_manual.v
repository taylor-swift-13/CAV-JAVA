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
From SimpleC.EE.CAV.verify_20260422_090412_array_swap_ends Require Import array_swap_ends_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma array_swap_ends_replace_nth_length :
  forall {A : Type} (n : nat) (x : A) (l : list A),
    length (replace_nth n x l) = length l.
Proof.
  intros A n x l.
  revert n.
  induction l; intros n; simpl.
  - destruct n; reflexivity.
  - destruct n; simpl; try reflexivity.
    rewrite IHl.
    reflexivity.
Qed.

Lemma array_swap_ends_nth_replace_nth_same :
  forall {A : Type} (l : list A) (n : nat) (x d : A),
    (n < length l)%nat ->
    nth n (replace_nth n x l) d = x.
Proof.
  intros A l n x d Hn.
  revert n Hn.
  induction l; intros n Hn; simpl in *.
  - lia.
  - destruct n; simpl.
    + reflexivity.
    + apply IHl.
      lia.
Qed.

Lemma array_swap_ends_nth_replace_nth_diff :
  forall {A : Type} (l : list A) (k i : nat) (x d : A),
    k <> i ->
    nth k (replace_nth i x l) d = nth k l d.
Proof.
  intros A l k i x d Hneq.
  revert k i Hneq.
  induction l; intros k i Hneq; simpl.
  - destruct k; destruct i; reflexivity.
  - destruct k; destruct i; simpl; try reflexivity.
    + contradiction.
    + apply IHl.
      lia.
Qed.

Lemma array_swap_ends_Zlength_replace_Znth :
  forall {A : Type} (i : Z) (x : A) (l : list A),
    Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A i x l.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  rewrite array_swap_ends_replace_nth_length.
  reflexivity.
Qed.

Lemma array_swap_ends_Znth_replace_Znth_same :
  forall {A : Type} (i : Z) (x d : A) (l : list A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i x l) d = x.
Proof.
  intros A i x d l Hi.
  unfold Znth, replace_Znth.
  apply array_swap_ends_nth_replace_nth_same.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma array_swap_ends_Znth_replace_Znth_diff :
  forall {A : Type} (k i : Z) (x d : A) (l : list A),
    0 <= k < Zlength l ->
    0 <= i ->
    k <> i ->
    Znth k (replace_Znth i x l) d = Znth k l d.
Proof.
  intros A k i x d l Hk Hi Hneq.
  unfold Znth, replace_Znth.
  apply array_swap_ends_nth_replace_nth_diff.
  lia.
Qed.

Lemma proof_of_array_swap_ends_return_wit_1 : array_swap_ends_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth (n_pre - 1) (Znth 0 l 0)
    (replace_Znth 0 (Znth (n_pre - 1) l 0) l)).
  entailer!.
  - intros i Hi.
    destruct Hi as [Hi_low Hi_high].
    split.
    + intro Hlt.
      lia.
    + intro Hge.
      split.
      * split.
        -- intro Hi0.
           subst i.
           rewrite array_swap_ends_Znth_replace_Znth_diff.
           ++ rewrite array_swap_ends_Znth_replace_Znth_same; lia.
           ++ rewrite array_swap_ends_Zlength_replace_Znth; lia.
           ++ lia.
           ++ lia.
        -- intro Hilast.
           subst i.
           rewrite array_swap_ends_Znth_replace_Znth_same.
           ++ reflexivity.
           ++ rewrite array_swap_ends_Zlength_replace_Znth; lia.
      * intros Hmid.
        destruct Hmid as [Hnot0 Hnotlast].
        rewrite array_swap_ends_Znth_replace_Znth_diff.
        -- rewrite array_swap_ends_Znth_replace_Znth_diff; lia.
        -- rewrite array_swap_ends_Zlength_replace_Znth; lia.
        -- lia.
        -- lia.
  - rewrite !array_swap_ends_Zlength_replace_Znth.
    lia.
Qed. 

Lemma proof_of_array_swap_ends_return_wit_2 : array_swap_ends_return_wit_2.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed. 
