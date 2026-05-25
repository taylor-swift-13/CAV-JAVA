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
From SimpleC.EE.CAV.verify_20260422_032621_array_count_increasing_steps Require Import array_count_increasing_steps_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_increasing_steps.
Local Open Scope sac.

Lemma sublist_prefix_full :
  forall {A} (l : list A) k,
    Zlength l <= k ->
    sublist 0 k l = l.
Proof.
  intros A l k Hk.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct in Hk.
  rewrite firstn_all2 by lia.
  reflexivity.
Qed.

Lemma array_count_increasing_steps_spec_short :
  forall (l : list Z),
    Zlength l <= 1 ->
    array_count_increasing_steps_spec l = 0.
Proof.
  intros l Hlen.
  destruct l.
  - reflexivity.
  - destruct l.
    + reflexivity.
    + simpl in Hlen.
      rewrite !Zlength_cons in Hlen.
      pose proof (Zlength_nonneg l).
      lia.
Qed.

Lemma array_count_increasing_steps_spec_app_single_cons :
  forall (p x y : Z) (l : list Z),
    array_count_increasing_steps_spec (p :: l ++ x :: y :: nil) =
    array_count_increasing_steps_spec (p :: l ++ x :: nil) +
    (if Z_lt_dec x y then 1 else 0).
Proof.
  intros p x y l.
  revert p x y.
  induction l; intros p x y.
  - simpl. destruct (Z_lt_dec p x); destruct (Z_lt_dec x y); lia.
  - simpl.
    pose proof (IHl a x y) as Hstep.
    simpl in Hstep.
    rewrite Hstep.
    lia.
Qed.

Lemma array_count_increasing_steps_spec_app_single :
  forall (l : list Z) (x y : Z),
    array_count_increasing_steps_spec (l ++ x :: y :: nil) =
    array_count_increasing_steps_spec (l ++ x :: nil) +
    (if Z_lt_dec x y then 1 else 0).
Proof.
  intros l x y.
  destruct l.
  - simpl. destruct (Z_lt_dec x y); lia.
  - apply array_count_increasing_steps_spec_app_single_cons.
Qed.

Lemma array_count_increasing_steps_spec_cons_bounds :
  forall (x : Z) (l : list Z),
    0 <= array_count_increasing_steps_spec (x :: l) <= Zlength l.
Proof.
  intros x l.
  revert x.
  induction l; intros x.
  - simpl. rewrite Zlength_nil. lia.
  - simpl.
    pose proof (IHl a) as Htail.
    simpl in Htail.
    rewrite Zlength_cons.
    destruct Htail as [IHlo IHhi].
    destruct (Z_lt_dec x a); lia.
Qed.

Lemma array_count_increasing_steps_spec_nonempty_bounds :
  forall (l : list Z),
    l <> nil ->
    0 <= array_count_increasing_steps_spec l <= Zlength l - 1.
Proof.
  intros l Hneq.
  destruct l.
  - contradiction.
  - pose proof (array_count_increasing_steps_spec_cons_bounds z l) as Hbounds.
    rewrite Zlength_cons.
    lia.
Qed.

Lemma array_count_increasing_steps_spec_step :
  forall (l : list Z) (i : Z),
    0 <= i ->
    i + 1 < Zlength l ->
    array_count_increasing_steps_spec (sublist 0 (i + 2) l) =
    array_count_increasing_steps_spec (sublist 0 (i + 1) l) +
    (if Z_lt_dec (Znth i l 0) (Znth (i + 1) l 0) then 1 else 0).
Proof.
  intros l i Hi Hlt.
  assert (Hprefix1 :
    sublist 0 (i + 1) l =
    sublist 0 i l ++ Znth i l 0 :: nil).
  {
    rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
    rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  assert (Hprefix2 :
    sublist 0 (i + 2) l =
    sublist 0 i l ++ Znth i l 0 :: Znth (i + 1) l 0 :: nil).
  {
    rewrite (sublist_split 0 (i + 2) (i + 1) l) by (pose proof Zlength_correct l; lia).
    replace (i + 2) with ((i + 1) + 1) by lia.
    rewrite (sublist_single (i + 1) l 0) by (rewrite <- Zlength_correct; lia).
    rewrite Hprefix1.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hprefix2.
  rewrite Hprefix1.
  rewrite array_count_increasing_steps_spec_app_single.
  reflexivity.
Qed.

Lemma proof_of_array_count_increasing_steps_safety_wit_7 : array_count_increasing_steps_safety_wit_7.
Proof.
  unfold array_count_increasing_steps_safety_wit_7.
  pre_process.
  prop_apply (store_int_range (&("n")) n_pre).
  Intros.
  assert (Hnmax : n_pre <= 2147483647).
  {
    match goal with
    | Hrange : Int.min_signed <= n_pre <= Int.max_signed |- _ =>
        change Int.max_signed with 2147483647 in Hrange;
        lia
    end.
  }
  assert (0 <= cnt <= i).
  {
    subst cnt.
    remember (sublist 0 (i + 1) l) as prefix eqn:Hprefix.
    assert (Hlenprefix : Zlength prefix = i + 1).
    {
      subst prefix.
      rewrite Zlength_sublist by lia.
      lia.
    }
    destruct prefix.
    - rewrite Zlength_nil in Hlenprefix.
      lia.
    - pose proof (array_count_increasing_steps_spec_nonempty_bounds (z :: prefix) ltac:(discriminate)) as Hbounds.
      rewrite Hlenprefix in Hbounds.
      lia.
  }
  entailer!; lia.
Qed.

Lemma proof_of_array_count_increasing_steps_entail_wit_1 : array_count_increasing_steps_entail_wit_1.
Proof.
  unfold array_count_increasing_steps_entail_wit_1.
  intros.
  entailer!.
  destruct l.
  - reflexivity.
  - destruct l.
    + reflexivity.
    + reflexivity.
Qed.

Lemma proof_of_array_count_increasing_steps_entail_wit_2_1 : array_count_increasing_steps_entail_wit_2_1.
Proof.
  unfold array_count_increasing_steps_entail_wit_2_1.
  intros.
  entailer!.
  subst cnt.
  replace ((i + 1) + 1) with (i + 2) by lia.
  rewrite array_count_increasing_steps_spec_step by lia.
  destruct (Z_lt_dec (Znth i l 0) (Znth (i + 1) l 0)); lia.
Qed.

Lemma proof_of_array_count_increasing_steps_entail_wit_2_2 : array_count_increasing_steps_entail_wit_2_2.
Proof.
  unfold array_count_increasing_steps_entail_wit_2_2.
  intros.
  entailer!.
  subst cnt.
  replace ((i + 1) + 1) with (i + 2) by lia.
  rewrite array_count_increasing_steps_spec_step by lia.
  destruct (Z_lt_dec (Znth i l 0) (Znth (i + 1) l 0)); lia.
Qed.

Lemma proof_of_array_count_increasing_steps_return_wit_1 : array_count_increasing_steps_return_wit_1.
Proof.
  unfold array_count_increasing_steps_return_wit_1.
  intros.
  entailer!.
  subst cnt.
  rewrite sublist_prefix_full by lia.
  reflexivity.
Qed.
