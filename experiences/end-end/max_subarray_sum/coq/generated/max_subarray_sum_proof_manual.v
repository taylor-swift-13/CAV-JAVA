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
From SimpleC.EE.CAV.verify_20260422_192331_max_subarray_sum Require Import max_subarray_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import max_subarray_sum.
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

Lemma sum_sublist_single_Z :
  forall (l : list Z) i,
    0 <= i < Zlength l ->
    sum (sublist i (i + 1) l) = Znth i l 0.
Proof.
  intros l i Hi.
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  lia.
Qed.

Lemma sum_sublist_snoc_Z :
  forall (l : list Z) lo i,
    0 <= lo ->
    lo < i ->
    i < Zlength l ->
    sum (sublist lo (i + 1) l) =
      sum (sublist lo i l) + Znth i l 0.
Proof.
  intros l lo i Hlo Hlt Hi.
  rewrite (sublist_split lo (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite sum_app.
  rewrite sum_sublist_single_Z by lia.
  lia.
Qed.

Lemma max_subarray_sum_spec_nonempty_acc :
  forall (l : list Z) n,
    1 <= n ->
    Zlength l = n ->
    max_subarray_sum_acc (Znth 0 l 0) (Znth 0 l 0) (sublist 1 n l) =
      max_subarray_sum_spec l.
Proof.
  intros l n Hn Hlen.
  destruct l.
  - rewrite Zlength_nil in Hlen. lia.
  - simpl.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons in *; lia).
    rewrite sublist_self by (rewrite Zlength_cons in Hlen; lia).
    reflexivity.
Qed.

Lemma max_subarray_sum_acc_step_cons :
  forall cur best x xs,
    max_subarray_sum_acc cur best (x :: xs) =
      max_subarray_sum_acc (Z.max x (cur + x))
        (Z.max best (Z.max x (cur + x))) xs.
Proof.
  intros. simpl. reflexivity.
Qed.

Ltac solve_cur_plus_range :=
  match goal with
  | Hsum : ?cur = sum (sublist ?lo ?i ?l),
    Hguard : forall lo0 hi0 : Z,
        _ -> _ <= sum (sublist lo0 hi0 ?l) <= _ |- _ =>
      pose proof (Hguard lo (i + 1) ltac:(lia)) as Hrange;
      rewrite sum_sublist_snoc_Z in Hrange by lia;
      rewrite <- Hsum in Hrange;
      lia
  end.

Ltac pose_singleton_range idx :=
  match goal with
  | Hguard : forall lo0 hi0 : Z,
      _ -> _ <= sum (sublist lo0 hi0 ?l) <= _ |- _ =>
      pose proof (Hguard idx (idx + 1) ltac:(lia)) as Hrange;
      rewrite sum_sublist_single_Z in Hrange by lia
  end.

Ltac pose_snoc_range lo i cur :=
  match goal with
  | Hsum : cur = sum (sublist lo i ?l),
    Hguard : forall lo0 hi0 : Z,
      _ -> _ <= sum (sublist lo0 hi0 ?l) <= _ |- _ =>
      pose proof (Hguard lo (i + 1) ltac:(lia)) as Hrange;
      rewrite sum_sublist_snoc_Z in Hrange by lia;
      rewrite <- Hsum in Hrange
  end.

Lemma proof_of_max_subarray_sum_safety_wit_4 : max_subarray_sum_safety_wit_4.
Proof.
  unfold max_subarray_sum_safety_wit_4.
  intros.
  entailer!.
  all: solve_cur_plus_range.
Qed. 

Lemma proof_of_max_subarray_sum_safety_wit_5 : max_subarray_sum_safety_wit_5.
Proof.
  unfold max_subarray_sum_safety_wit_5.
  intros.
  entailer!.
  all: solve_cur_plus_range.
Qed. 

Lemma proof_of_max_subarray_sum_entail_wit_1 : max_subarray_sum_entail_wit_1.
Proof.
  unfold max_subarray_sum_entail_wit_1.
  intros.
  Exists 0.
  entailer!.
  - apply max_subarray_sum_spec_nonempty_acc; lia.
  - pose_singleton_range 0.
    lia.
  - pose_singleton_range 0.
    lia.
  - pose_singleton_range 0.
    lia.
  - pose_singleton_range 0.
    lia.
  - rewrite <- sum_sublist_single_Z by lia.
    reflexivity.
Qed. 

Lemma proof_of_max_subarray_sum_entail_wit_2_1 : max_subarray_sum_entail_wit_2_1.
Proof.
  unfold max_subarray_sum_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  - match goal with
    | Hacc : max_subarray_sum_acc cur best (sublist i n_pre l) =
             max_subarray_sum_spec l |- _ =>
        rewrite sublist_head_cons_Z in Hacc by lia;
        rewrite max_subarray_sum_acc_step_cons in Hacc;
        replace (Z.max (Znth i l 0) (cur + Znth i l 0))
          with (Znth i l 0) in Hacc by lia;
        replace (Z.max best (Znth i l 0))
          with (Znth i l 0) in Hacc by lia;
        exact Hacc
    end.
  - pose_singleton_range i.
    lia.
  - pose_singleton_range i.
    lia.
  - rewrite <- sum_sublist_single_Z by lia.
    reflexivity.
Qed. 

Lemma proof_of_max_subarray_sum_entail_wit_2_2 : max_subarray_sum_entail_wit_2_2.
Proof.
  unfold max_subarray_sum_entail_wit_2_2.
  intros.
  Exists lo_3.
  entailer!.
  - match goal with
    | Hacc : max_subarray_sum_acc cur best (sublist i n_pre l) =
             max_subarray_sum_spec l |- _ =>
        rewrite sublist_head_cons_Z in Hacc by lia;
        rewrite max_subarray_sum_acc_step_cons in Hacc;
        replace (Z.max (Znth i l 0) (cur + Znth i l 0))
          with (cur + Znth i l 0) in Hacc by lia;
        replace (Z.max best (cur + Znth i l 0))
          with (cur + Znth i l 0) in Hacc by lia;
        exact Hacc
    end.
  - pose_snoc_range lo_3 i cur.
    lia.
  - pose_snoc_range lo_3 i cur.
    lia.
  - rewrite sum_sublist_snoc_Z by lia.
    lia.
Qed. 

Lemma proof_of_max_subarray_sum_entail_wit_2_3 : max_subarray_sum_entail_wit_2_3.
Proof.
  unfold max_subarray_sum_entail_wit_2_3.
  intros.
  Exists lo_3.
  entailer!.
  - match goal with
    | Hacc : max_subarray_sum_acc cur best (sublist i n_pre l) =
             max_subarray_sum_spec l |- _ =>
        rewrite sublist_head_cons_Z in Hacc by lia;
        rewrite max_subarray_sum_acc_step_cons in Hacc;
        replace (Z.max (Znth i l 0) (cur + Znth i l 0))
          with (cur + Znth i l 0) in Hacc by lia;
        replace (Z.max best (cur + Znth i l 0))
          with best in Hacc by lia;
        exact Hacc
    end.
  - pose_snoc_range lo_3 i cur.
    lia.
  - rewrite sum_sublist_snoc_Z by lia.
    lia.
Qed. 

Lemma proof_of_max_subarray_sum_entail_wit_2_4 : max_subarray_sum_entail_wit_2_4.
Proof.
  unfold max_subarray_sum_entail_wit_2_4.
  intros.
  Exists i.
  entailer!.
  - match goal with
    | Hacc : max_subarray_sum_acc cur best (sublist i n_pre l) =
             max_subarray_sum_spec l |- _ =>
        rewrite sublist_head_cons_Z in Hacc by lia;
        rewrite max_subarray_sum_acc_step_cons in Hacc;
        replace (Z.max (Znth i l 0) (cur + Znth i l 0))
          with (Znth i l 0) in Hacc by lia;
        replace (Z.max best (Znth i l 0))
          with best in Hacc by lia;
        exact Hacc
    end.
  - pose_singleton_range i.
    lia.
  - rewrite <- sum_sublist_single_Z by lia.
    reflexivity.
Qed. 

Lemma proof_of_max_subarray_sum_return_wit_1 : max_subarray_sum_return_wit_1.
Proof.
  unfold max_subarray_sum_return_wit_1.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  match goal with
  | Hacc : max_subarray_sum_acc cur best (sublist n_pre n_pre l) =
           max_subarray_sum_spec l |- _ =>
      rewrite sublist_nil in Hacc by lia;
      simpl in Hacc;
      exact Hacc
  end.
Qed. 
