Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic StoreAux.
From SimpleC.EE.CAV.verify_20260422_171952_house_robber Require Import house_robber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import house_robber.

Fixpoint house_robber_state (prev2 prev1 : Z) (l : list Z) : Z * Z :=
  match l with
  | nil => (prev2, prev1)
  | x :: xs =>
      let take := prev2 + x in
      let cur := Z.max take prev1 in
      house_robber_state prev1 cur xs
  end.

Lemma house_robber_state_snd_acc :
  forall l prev2 prev1,
    snd (house_robber_state prev2 prev1 l) =
    house_robber_acc prev2 prev1 l.
Proof.
  induction l; intros prev2 prev1; simpl; auto.
Qed.

Lemma house_robber_state_app :
  forall l1 l2 prev2 prev1,
    house_robber_state prev2 prev1 (l1 ++ l2) =
    let st := house_robber_state prev2 prev1 l1 in
    house_robber_state (fst st) (snd st) l2.
Proof.
  induction l1; intros l2 prev2 prev1; simpl; auto.
Qed.

Lemma house_robber_state_fst_snoc :
  forall l x prev2 prev1,
    fst (house_robber_state prev2 prev1 (l ++ x :: nil)) =
    snd (house_robber_state prev2 prev1 l).
Proof.
  intros.
  rewrite house_robber_state_app.
  destruct (house_robber_state prev2 prev1 l).
  simpl. reflexivity.
Qed.

Lemma house_robber_spec_state_snd :
  forall l,
    snd (house_robber_state 0 0 l) = house_robber_spec l.
Proof.
  intros. unfold house_robber_spec. apply house_robber_state_snd_acc.
Qed.

Lemma house_robber_spec_snoc_state :
  forall l x,
    house_robber_spec (l ++ x :: nil) =
    Z.max (fst (house_robber_state 0 0 l) + x)
          (snd (house_robber_state 0 0 l)).
Proof.
  intros.
  unfold house_robber_spec.
  rewrite <- house_robber_state_snd_acc.
  rewrite house_robber_state_app.
  destruct (house_robber_state 0 0 l).
  simpl. reflexivity.
Qed.

Lemma house_robber_state_fst_prefix :
  forall l i,
    0 < i ->
    i <= Zlength l ->
    fst (house_robber_state 0 0 (sublist 0 i l)) =
    house_robber_spec (sublist 0 (i - 1) l).
Proof.
  intros l i Hlo Hhi.
  rewrite (sublist_split 0 i (i - 1) l).
  2: lia.
  2: { rewrite Zlength_correct in Hhi. lia. }
  replace (sublist (i - 1) i l) with (Znth (i - 1) l 0 :: nil).
  rewrite house_robber_state_fst_snoc.
  apply house_robber_spec_state_snd.
  replace (sublist (i - 1) i l) with (sublist (i - 1) (i - 1 + 1) l) by (f_equal; lia).
  rewrite (sublist_single (i - 1) l 0) by (rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.

Lemma house_robber_prefix_step :
  forall l i prev2 prev1,
    0 <= i ->
    i < Zlength l ->
    prev1 = house_robber_spec (sublist 0 i l) ->
    (i = 0 -> prev2 = 0) ->
    (i > 0 -> prev2 = house_robber_spec (sublist 0 (i - 1) l)) ->
    house_robber_spec (sublist 0 (i + 1) l) =
    Z.max (prev2 + Znth i l 0) prev1.
Proof.
  intros l i prev2 prev1 Hlo Hhi Hprev1 Hprev2_zero Hprev2_pos.
  rewrite (sublist_split 0 (i + 1) i l).
  2: lia.
  2: { rewrite Zlength_correct in Hhi. lia. }
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite house_robber_spec_snoc_state.
  rewrite house_robber_spec_state_snd.
  rewrite Hprev1.
  destruct (Z.eq_dec i 0).
  - subst i. simpl. rewrite Hprev2_zero by reflexivity. lia.
  - assert (0 < i) by lia.
    rewrite house_robber_state_fst_prefix by lia.
    rewrite Hprev2_pos by lia.
    reflexivity.
Qed.

Lemma house_robber_next_take_bound :
  forall l n i prev1,
    Zlength l = n ->
    (forall k : Z,
      0 <= k /\ k <= n ->
      0 <= house_robber_spec (sublist 0 k l) /\
      house_robber_spec (sublist 0 k l) <= INT_MAX) ->
    0 <= i ->
    i + 1 < n ->
    prev1 = house_robber_spec (sublist 0 i l) ->
    prev1 + Znth (i + 1) l 0 <= INT_MAX.
Proof.
  intros l n i prev1 Hlen Hbound Hlo Hnext Hprev1.
  assert (Hspec_bound: house_robber_spec (sublist 0 (i + 2) l) <= INT_MAX).
  { pose proof (Hbound (i + 2) ltac:(lia)) as [_ Hle]. exact Hle. }
  assert (Hzero: i + 1 = 0 -> prev1 = 0) by (intro Hfalse; lia).
  assert (Hpos:
    i + 1 > 0 ->
    prev1 = house_robber_spec (sublist 0 (i + 1 - 1) l)).
  { intro Hgt. rewrite Hprev1.
    replace (i + 1 - 1) with i.
    - reflexivity.
    - lia. }
  pose proof (house_robber_prefix_step l (i + 1) prev1
                (house_robber_spec (sublist 0 (i + 1) l))
                ltac:(lia) ltac:(lia) eq_refl Hzero Hpos)
    as Hstep.
  replace (i + 2) with (i + 1 + 1) in Hspec_bound by lia.
  rewrite Hstep in Hspec_bound.
  pose proof (Z.le_max_l (prev1 + Znth (i + 1) l 0)
                         (house_robber_spec (sublist 0 (i + 1) l))).
  lia.
Qed.

Lemma house_robber_full_sublist :
  forall l n i,
    Zlength l = n ->
    i >= n ->
    i <= n ->
    house_robber_spec (sublist 0 i l) = house_robber_spec l.
Proof.
  intros l n i Hlen Hge Hle.
  assert (i = n) by lia. subst i.
  replace n with (Zlength l) by lia.
  rewrite sublist_self; reflexivity.
Qed.

Local Open Scope sac.

Lemma proof_of_house_robber_safety_wit_4 : house_robber_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - destruct (Z.eq_dec i 0).
    + subst i. pose proof (H8 eq_refl). subst prev2.
      pose proof (H5 0 ltac:(lia)) as [Hz _]. lia.
    + assert (0 < i) by lia.
      pose proof (H9 ltac:(lia)).
      subst prev2.
      pose proof (H6 (i - 1) ltac:(lia)) as [Hprev2_nonneg _].
      pose proof (H5 i ltac:(lia)) as [Hz _].
      lia.
Qed.

Lemma proof_of_house_robber_entail_wit_1 : house_robber_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - intro Hn.
    pose proof (H2 0 ltac:(lia)) as [_ Hle].
    lia.
Qed.

Lemma proof_of_house_robber_entail_wit_2_1 : house_robber_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    entailer!.
  - intro Hnext.
    apply house_robber_next_take_bound with (n := n_pre) (i := i_2); auto; lia.
  - intro Hpos.
    replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
  - rewrite (house_robber_prefix_step l i_2 prev2 prev1);
      try assumption; try lia.
Qed.

Lemma proof_of_house_robber_entail_wit_2_2 : house_robber_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    entailer!.
  - intro Hnext.
    apply house_robber_next_take_bound with (n := n_pre) (i := i_2); auto; lia.
  - intro Hpos.
    replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
  - rewrite (house_robber_prefix_step l i_2 prev2 prev1);
      try assumption; try lia.
Qed.

Lemma proof_of_house_robber_return_wit_1 : house_robber_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst prev1.
  apply house_robber_full_sublist with (n := n_pre); lia.
Qed.
