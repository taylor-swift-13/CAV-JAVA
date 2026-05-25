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
From SimpleC.EE.CAV.verify_20260422_063947_array_prefix_max Require Import array_prefix_max_goal.
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

Lemma Zlength_replace_Znth :
  forall {A : Type} (i : Z) (x : A) (l : list A),
    Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A i x l.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  rewrite length_replace_nth.
  reflexivity.
Qed.

Lemma Znth_replace_Znth_same :
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

Lemma Znth_replace_Znth_diff :
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

Lemma proof_of_array_prefix_max_entail_wit_1 : array_prefix_max_entail_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth 0 (Znth 0 la 0) lo).
  entailer!.
  - intros p Hp.
    rewrite Znth_replace_Znth_diff by lia.
    reflexivity.
  - intros p Hp.
    assert (p = 0) by lia.
    subst p.
    exists 0.
    rewrite Znth_replace_Znth_same by lia.
    split.
    + lia.
    + intros k Hk.
      assert (k = 0) by lia.
      subst k.
      lia.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    lia.
  - rewrite Znth_replace_Znth_same by lia.
    reflexivity.
  - rewrite Zlength_replace_Znth.
    lia.
Qed. 

Lemma proof_of_array_prefix_max_entail_wit_2_1 : array_prefix_max_entail_wit_2_1.
Proof.
  pre_process.
  Exists (replace_Znth i cur lr_2).
  entailer!.
  - intros p Hp.
    rewrite Znth_replace_Znth_diff by lia.
    apply H9. lia.
  - intros p Hp.
    destruct (Z.eq_dec p i) as [Heq | Hneq].
    + subst p.
      rewrite Znth_replace_Znth_same by lia.
      rewrite H6.
      pose proof (H8 (i - 1) ltac:(lia)) as [j0 [Hex Hmax]].
      destruct Hex as [Hjrange Hval].
      exists j0.
      split.
      * split.
        -- lia.
        -- exact Hval.
      * intros k Hk.
        destruct (Z.eq_dec k i) as [Hki | Hki].
        -- subst k. lia.
        -- apply Hmax; lia.
    + rewrite Znth_replace_Znth_diff by lia.
      apply H8. lia.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [Heq | Hneq].
    + subst k. lia.
    + apply H7. lia.
  - replace (i + 1 - 1) with i by lia.
    rewrite Znth_replace_Znth_same by lia.
    reflexivity.
  - rewrite Zlength_replace_Znth. lia.
Qed. 

Lemma proof_of_array_prefix_max_entail_wit_2_2 : array_prefix_max_entail_wit_2_2.
Proof.
  pre_process.
  Exists (replace_Znth i (Znth i la 0) lr_2).
  entailer!.
  - intros p Hp.
    rewrite Znth_replace_Znth_diff by lia.
    apply H9. lia.
  - intros p Hp.
    destruct (Z.eq_dec p i) as [Heq | Hneq].
    + subst p.
      rewrite Znth_replace_Znth_same by lia.
      exists i.
      split.
      * split.
        -- lia.
        -- reflexivity.
      * intros k Hk.
        destruct (Z.eq_dec k i) as [Hki | Hki].
        -- subst k. lia.
        -- specialize (H7 k ltac:(lia)).
           lia.
    + rewrite Znth_replace_Znth_diff by lia.
      apply H8. lia.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [Heq | Hneq].
    + subst k. lia.
    + specialize (H7 k ltac:(lia)).
      lia.
  - replace (i + 1 - 1) with i by lia.
    rewrite Znth_replace_Znth_same by lia.
    reflexivity.
  - rewrite Zlength_replace_Znth. lia.
Qed. 

Lemma proof_of_array_prefix_max_return_wit_1 : array_prefix_max_return_wit_1.
Proof.
  pre_process.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  Exists lr_2.
  entailer!.
Qed. 

Lemma proof_of_array_prefix_max_return_wit_2 : array_prefix_max_return_wit_2.
Proof.
  pre_process.
  Exists lo.
  entailer!.
Qed. 
