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
From SimpleC.EE.CAV.verify_20260422_201546_min_cost_two_steps Require Import min_cost_two_steps_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import min_cost_two_steps.

Fixpoint min_cost_two_steps_state (prev2 prev1 : Z) (l : list Z) : Z * Z :=
  match l with
  | nil => (prev2, prev1)
  | x :: xs =>
      let cur := Z.min prev1 prev2 + x in
      min_cost_two_steps_state prev1 cur xs
  end.

Lemma min_cost_two_steps_state_snd_acc :
  forall l prev2 prev1,
    snd (min_cost_two_steps_state prev2 prev1 l) =
    min_cost_two_steps_acc prev2 prev1 l.
Proof.
  induction l; intros prev2 prev1; simpl; auto.
Qed.

Lemma min_cost_two_steps_state_app :
  forall l1 l2 prev2 prev1,
    min_cost_two_steps_state prev2 prev1 (l1 ++ l2) =
    let st := min_cost_two_steps_state prev2 prev1 l1 in
    min_cost_two_steps_state (fst st) (snd st) l2.
Proof.
  induction l1; intros l2 prev2 prev1; simpl; auto.
Qed.

Lemma min_cost_two_steps_state_fst_snoc :
  forall l x prev2 prev1,
    fst (min_cost_two_steps_state prev2 prev1 (l ++ x :: nil)) =
    snd (min_cost_two_steps_state prev2 prev1 l).
Proof.
  intros.
  rewrite min_cost_two_steps_state_app.
  destruct (min_cost_two_steps_state prev2 prev1 l).
  simpl. reflexivity.
Qed.

Lemma min_cost_two_steps_prefix_one :
  forall l,
    1 <= Zlength l ->
    min_cost_two_steps_spec (sublist 0 1 l) = Znth 0 l 0.
Proof.
  intros l Hlen.
  replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
  2: {
    replace 1 with (0 + 1) by lia.
    rewrite (sublist_single 0 l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  simpl. reflexivity.
Qed.

Lemma min_cost_two_steps_sublist_first_two :
  forall l i,
    2 <= i ->
    i <= Zlength l ->
    sublist 0 i l =
      Znth 0 l 0 :: Znth 1 l 0 :: sublist 2 i l.
Proof.
  intros l i Hlo Hhi.
  rewrite (sublist_split 0 i 1 l) by (rewrite Zlength_correct in Hhi; lia).
  replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
  2: {
    replace 1 with (0 + 1) by lia.
    rewrite (sublist_single 0 l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  rewrite (sublist_split 1 i 2 l) by (rewrite Zlength_correct in Hhi; lia).
  replace (sublist 1 2 l) with (Znth 1 l 0 :: nil).
  2: {
    replace 2 with (1 + 1) by lia.
    rewrite (sublist_single 1 l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  reflexivity.
Qed.

Lemma min_cost_two_steps_spec_prefix_ge2 :
  forall l i,
    2 <= i ->
    i <= Zlength l ->
    min_cost_two_steps_spec (sublist 0 i l) =
    min_cost_two_steps_acc (Znth 0 l 0) (Znth 0 l 0 + Znth 1 l 0)
                           (sublist 2 i l).
Proof.
  intros l i Hlo Hhi.
  unfold min_cost_two_steps_spec.
  rewrite min_cost_two_steps_sublist_first_two by lia.
  simpl. reflexivity.
Qed.

Lemma min_cost_two_steps_state_snd_prefix :
  forall l i,
    2 <= i ->
    i <= Zlength l ->
    snd (min_cost_two_steps_state (Znth 0 l 0) (Znth 0 l 0 + Znth 1 l 0)
                                  (sublist 2 i l)) =
    min_cost_two_steps_spec (sublist 0 i l).
Proof.
  intros.
  rewrite min_cost_two_steps_state_snd_acc.
  symmetry. apply min_cost_two_steps_spec_prefix_ge2; lia.
Qed.

Lemma min_cost_two_steps_state_fst_prefix :
  forall l i,
    2 <= i ->
    i <= Zlength l ->
    fst (min_cost_two_steps_state (Znth 0 l 0) (Znth 0 l 0 + Znth 1 l 0)
                                  (sublist 2 i l)) =
    min_cost_two_steps_spec (sublist 0 (i - 1) l).
Proof.
  intros l i Hlo Hhi.
  destruct (Z.eq_dec i 2) as [Hi | Hi].
  - subst i.
    rewrite sublist_nil by lia.
    simpl.
    rewrite min_cost_two_steps_prefix_one by lia.
    reflexivity.
  - assert (2 < i) by lia.
    rewrite (sublist_split 2 i (i - 1) l).
    2: lia.
    2: { rewrite Zlength_correct in Hhi; lia. }
    replace (sublist (i - 1) i l) with (Znth (i - 1) l 0 :: nil).
    2: {
      replace (sublist (i - 1) i l) with (sublist (i - 1) ((i - 1) + 1) l) by (f_equal; lia).
      symmetry. apply sublist_single. rewrite <- Zlength_correct; lia.
    }
    rewrite min_cost_two_steps_state_fst_snoc.
    apply min_cost_two_steps_state_snd_prefix; lia.
Qed.

Lemma min_cost_two_steps_prefix_step :
  forall l i,
    2 <= i ->
    i < Zlength l ->
    min_cost_two_steps_spec (sublist 0 (i + 1) l) =
    Z.min (min_cost_two_steps_spec (sublist 0 i l))
          (min_cost_two_steps_spec (sublist 0 (i - 1) l)) +
    Znth i l 0.
Proof.
  intros l i Hlo Hhi.
  rewrite min_cost_two_steps_spec_prefix_ge2 by lia.
  rewrite (sublist_split 2 (i + 1) i l).
  2: lia.
  2: { rewrite Zlength_correct in Hhi; lia. }
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  2: {
    symmetry. apply sublist_single. rewrite <- Zlength_correct; lia.
  }
  rewrite <- min_cost_two_steps_state_snd_acc.
  rewrite min_cost_two_steps_state_app.
  rewrite min_cost_two_steps_state_snd_acc.
  rewrite min_cost_two_steps_state_fst_prefix by lia.
  rewrite min_cost_two_steps_state_snd_prefix by lia.
  simpl. reflexivity.
Qed.

Lemma min_cost_two_steps_acc_bound :
  forall xs prev2 prev1 base,
    0 <= prev2 ->
    0 <= prev1 ->
    prev2 <= base ->
    prev1 <= base ->
    (forall j, 0 <= j -> j < Zlength xs -> 0 <= Znth j xs 0) ->
    0 <= min_cost_two_steps_acc prev2 prev1 xs /\
    min_cost_two_steps_acc prev2 prev1 xs <= base + sum xs.
Proof.
  induction xs; intros prev2 prev1 base Hprev2 Hprev1 Hle2 Hle1 Hnonneg.
  - simpl. lia.
  - assert (Hx: 0 <= a).
    {
      assert (Hlen0: 0 < Zlength (a :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      pose proof (Hnonneg 0 ltac:(lia) Hlen0) as Hx0.
      rewrite Znth0_cons in Hx0. exact Hx0.
    }
    simpl.
    replace (base + (a + sum xs)) with (base + a + sum xs) by lia.
    apply IHxs with (base := base + a).
    + exact Hprev1.
    + pose proof (Z.min_glb_l prev1 prev2).
      lia.
    + lia.
    + pose proof (Z.min_glb_l prev1 prev2).
      lia.
    + intros j Hjlo Hjhi.
      specialize (Hnonneg (j + 1)).
      simpl in Hnonneg.
      rewrite Znth_cons in Hnonneg by lia.
      replace (j + 1 - 1) with j in Hnonneg by lia.
      apply Hnonneg.
      * lia.
      * rewrite Zlength_cons; lia.
Qed.

Lemma min_cost_two_steps_prefix_bound :
  forall l k,
    1 <= k ->
    k <= Zlength l ->
    (forall i, 0 <= i -> i < Zlength l -> 0 <= Znth i l 0) ->
    0 <= min_cost_two_steps_spec (sublist 0 k l) /\
    min_cost_two_steps_spec (sublist 0 k l) <= sum (sublist 0 k l).
Proof.
  intros l k Hklo Hkhi Hnonneg.
  destruct (Z.eq_dec k 1) as [Hk1 | Hk1].
  - subst k.
    rewrite min_cost_two_steps_prefix_one by lia.
    replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
    2: {
      replace 1 with (0 + 1) by lia.
      symmetry. apply sublist_single. rewrite <- Zlength_correct; lia.
    }
    simpl.
    pose proof (Hnonneg 0 ltac:(lia) ltac:(lia)).
    lia.
  - assert (2 <= k) by lia.
    rewrite min_cost_two_steps_spec_prefix_ge2 by lia.
    rewrite min_cost_two_steps_sublist_first_two by lia.
    simpl sum.
    replace (Znth 0 l 0 + (Znth 1 l 0 + sum (sublist 2 k l)))
      with (Znth 0 l 0 + Znth 1 l 0 + sum (sublist 2 k l)) by lia.
    apply min_cost_two_steps_acc_bound.
    + apply Hnonneg; lia.
    + pose proof (Hnonneg 0 ltac:(lia) ltac:(lia)).
      pose proof (Hnonneg 1 ltac:(lia) ltac:(lia)).
      lia.
    + pose proof (Hnonneg 1 ltac:(lia) ltac:(lia)).
      lia.
    + lia.
    + intros j Hjlo Hjhi.
      assert (Hsub_len: Zlength (sublist 2 k l) = k - 2).
      { rewrite Zlength_sublist by lia. lia. }
      rewrite Znth_sublist by lia.
      apply Hnonneg.
      * lia.
      * lia.
Qed.

Lemma min_cost_two_steps_full_sublist :
  forall l n i,
    Zlength l = n ->
    i >= n ->
    i <= n ->
    min_cost_two_steps_spec (sublist 0 i l) = min_cost_two_steps_spec l.
Proof.
  intros l n i Hlen Hge Hle.
  assert (i = n) by lia. subst i.
  replace n with (Zlength l) by lia.
  rewrite sublist_self; reflexivity.
Qed.

Local Open Scope sac.

Lemma proof_of_min_cost_two_steps_safety_wit_4 : min_cost_two_steps_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - pose proof (H3 0 ltac:(lia)) as [Hz0 _].
    pose proof (H3 1 ltac:(lia)) as [Hz1 _].
    lia.
  - pose proof (H4 2 ltac:(lia)) as [_ Hsum].
    replace (sublist 0 2 l) with (Znth 0 l 0 :: Znth 1 l 0 :: nil) in Hsum.
    + simpl in Hsum. lia.
    + rewrite min_cost_two_steps_sublist_first_two by lia.
      rewrite sublist_nil by lia. reflexivity.
Qed.

Lemma proof_of_min_cost_two_steps_safety_wit_8 : min_cost_two_steps_safety_wit_8.
Proof.
  pre_process.
  entailer!.
  - pose proof (H15 i ltac:(lia)) as [Hxi _].
    lia.
  - subst prev1.
    pose proof (H6 i ltac:(lia)) as [_ Hspec].
    pose proof (H5 (i + 1) ltac:(lia)) as [_ Hsum_next].
    pose proof (H4 i ltac:(lia)) as [_ Hxi].
    rewrite (sublist_split 0 (i + 1) i l) in Hsum_next.
    2: lia.
    2: { rewrite Zlength_correct in H3; lia. }
    rewrite (sublist_single i l 0) in Hsum_next by (rewrite <- Zlength_correct; lia).
    rewrite sum_app in Hsum_next. simpl in Hsum_next. lia.
Qed.

Lemma proof_of_min_cost_two_steps_safety_wit_9 : min_cost_two_steps_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  - pose proof (H15 i ltac:(lia)) as [Hxi _].
    lia.
  - subst prev2.
    pose proof (H6 (i - 1) ltac:(lia)) as [_ Hspec].
    pose proof (H5 (i + 1) ltac:(lia)) as [_ Hsum_next].
    pose proof (H4 i ltac:(lia)) as [_ Hxi].
    rewrite (sublist_split 0 (i + 1) i l) in Hsum_next.
    2: lia.
    2: { rewrite Zlength_correct in H3; lia. }
    rewrite (sublist_single i l 0) in Hsum_next by (rewrite <- Zlength_correct; lia).
    rewrite sum_app in Hsum_next. simpl in Hsum_next.
    assert (sum (sublist 0 (i - 1) l) <= sum (sublist 0 i l)).
    {
      rewrite (sublist_split 0 i (i - 1) l).
      2: lia.
      2: { rewrite Zlength_correct in H3; lia. }
      replace (sublist (i - 1) i l) with (Znth (i - 1) l 0 :: nil).
      2: {
        replace (sublist (i - 1) i l) with (sublist (i - 1) ((i - 1) + 1) l) by (f_equal; lia).
        symmetry. apply sublist_single. rewrite <- Zlength_correct; lia.
      }
      rewrite sum_app. simpl.
      pose proof (H4 (i - 1) ltac:(lia)) as [Hxim1 _].
      lia.
    }
    lia.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_1 : min_cost_two_steps_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - pose proof (H3 0 ltac:(lia)) as [Hz _].
    pose proof (H3 1 ltac:(lia)) as [Ho _].
    lia.
  - pose proof (H3 0 ltac:(lia)) as [Hz _].
    exact Hz.
  - rewrite min_cost_two_steps_spec_prefix_ge2 by lia.
    rewrite sublist_nil by lia.
    simpl. reflexivity.
  - rewrite min_cost_two_steps_prefix_one by lia.
    reflexivity.
  - intros k Hkrange.
    apply min_cost_two_steps_prefix_bound; try lia.
    intros idx Hidxlo Hidxhi.
    pose proof (H3 idx ltac:(lia)) as [Hz _].
    exact Hz.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_2_1 : min_cost_two_steps_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - pose proof (H4 i_2 ltac:(lia)) as [Hxi _].
    lia.
  - rewrite (min_cost_two_steps_prefix_step l i_2) by lia.
    subst prev1 prev2.
    rewrite Z.min_l by lia.
    reflexivity.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_2_2 : min_cost_two_steps_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - pose proof (H4 i_2 ltac:(lia)) as [Hxi _].
    lia.
  - rewrite (min_cost_two_steps_prefix_step l i_2) by lia.
    subst prev1 prev2.
    rewrite Z.min_r by lia.
    reflexivity.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
Qed.

Lemma proof_of_min_cost_two_steps_return_wit_2 : min_cost_two_steps_return_wit_2.
Proof.
  pre_process.
  entailer!.
  subst prev1.
  apply min_cost_two_steps_full_sublist with (n := n_pre); lia.
Qed.
