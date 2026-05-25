Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
From AUXLib Require Import ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260422_033321_array_count_transitions Require Import array_count_transitions_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_transitions.
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

Lemma sublist_prefix_snoc_Z :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ (Znth i l 0 :: nil).
Proof.
  intros l i Hi.
  rewrite (@sublist_split Z 0 (i + 1) i l).
  2: lia.
  2: rewrite <- Zlength_correct; lia.
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.

Lemma last_sublist_prefix_Z :
  forall (l : list Z) (i : Z),
    1 <= i <= Zlength l ->
    last (sublist 0 i l) 0 = Znth (i - 1) l 0.
Proof.
  intros l i Hi.
  replace i with ((i - 1) + 1) at 1 by lia.
  rewrite sublist_prefix_snoc_Z by lia.
  rewrite last_last.
  reflexivity.
Qed.

Lemma array_count_transitions_from_snoc :
  forall (prev y : Z) (xs : list Z),
    array_count_transitions_from prev (xs ++ (y :: nil)) =
    array_count_transitions_from prev xs +
    (if Z.eq_dec y (last (prev :: xs) 0) then 0 else 1).
Proof.
  intros prev y xs.
  revert prev.
  induction xs; intros prev.
  - simpl.
    destruct (Z.eq_dec y prev); lia.
  - simpl.
    rewrite IHxs.
    simpl.
    destruct (Z.eq_dec a prev); destruct (Z.eq_dec y (last (a :: xs) 0)); lia.
Qed.

Lemma last_nonempty_default_indep_Z :
  forall (xs : list Z) (d1 d2 : Z),
    xs <> nil ->
    last xs d1 = last xs d2.
Proof.
  intros xs d1 d2 Hnonempty.
  destruct xs.
  - contradiction.
  - clear Hnonempty.
    revert z d1 d2.
    induction xs; intros x d1 d2.
    + reflexivity.
    + simpl. apply IHxs.
Qed.

Lemma array_count_transitions_spec_snoc_nonempty :
  forall (xs : list Z) (y d : Z),
    xs <> nil ->
    array_count_transitions_spec (xs ++ (y :: nil)) =
    array_count_transitions_spec xs +
    (if Z.eq_dec y (last xs d) then 0 else 1).
Proof.
  intros xs y d Hnonempty.
  destruct xs.
  - contradiction.
  - simpl.
    rewrite array_count_transitions_from_snoc.
    replace (last (z :: xs) 0) with (last (z :: xs) d).
    + reflexivity.
    + apply last_nonempty_default_indep_Z. discriminate.
Qed.

Lemma sublist_prefix_nonempty_Z :
  forall (l : list Z) (i : Z),
    1 <= i <= Zlength l ->
    sublist 0 i l <> nil.
Proof.
  intros l i Hi Hnil.
  pose proof (Zlength_sublist0 i l ltac:(lia)) as Hlen.
  rewrite Hnil in Hlen.
  rewrite Zlength_nil in Hlen.
  lia.
Qed.

Lemma array_count_transitions_spec_step :
  forall (l : list Z) (i : Z),
    1 <= i ->
    i < Zlength l ->
    array_count_transitions_spec (sublist 0 (i + 1) l) =
    array_count_transitions_spec (sublist 0 i l) +
    (if Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0) then 0 else 1).
Proof.
  intros l i Hi Hlt.
  rewrite sublist_prefix_snoc_Z by lia.
  rewrite array_count_transitions_spec_snoc_nonempty with (d := 0).
  - rewrite last_sublist_prefix_Z by lia.
    reflexivity.
  - apply sublist_prefix_nonempty_Z; lia.
Qed.

Lemma array_count_transitions_spec_cons_bounds :
  forall (x : Z) (l : list Z),
    0 <= array_count_transitions_spec (x :: l) <= Zlength l.
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
    destruct (Z.eq_dec a x); lia.
Qed.

Lemma array_count_transitions_spec_bounds :
  forall (l : list Z),
    0 <= array_count_transitions_spec l <= Z.max 0 (Zlength l - 1).
Proof.
  intros l.
  destruct l.
  - simpl. lia.
  - pose proof (array_count_transitions_spec_cons_bounds z l) as Hbounds.
    rewrite Zlength_cons.
    lia.
Qed.

Lemma proof_of_array_count_transitions_safety_wit_5 : array_count_transitions_safety_wit_5.
Proof.
  unfold array_count_transitions_safety_wit_5.
  pre_process.
  prop_apply (store_int_range (&("n")) n_pre).
  Intros.
  change Int.min_signed with (-2147483648) in H7.
  change Int.max_signed with 2147483647 in H7.
  assert (0 <= cnt <= i - 1).
  {
    subst cnt.
    pose proof (array_count_transitions_spec_bounds (sublist 0 i l)) as Hbounds.
    rewrite Zlength_sublist in Hbounds by lia.
    replace (i - 0) with i in Hbounds by lia.
    replace (Z.max 0 (i - 1)) with (i - 1) in Hbounds by lia.
    exact Hbounds.
  }
  entailer!; lia.
Qed. 

Lemma proof_of_array_count_transitions_entail_wit_1 : array_count_transitions_entail_wit_1.
Proof.
  unfold array_count_transitions_entail_wit_1.
  intros.
  entailer!.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed. 

Lemma proof_of_array_count_transitions_entail_wit_2_1 : array_count_transitions_entail_wit_2_1.
Proof.
  unfold array_count_transitions_entail_wit_2_1.
  intros.
  entailer!.
  subst cnt.
  rewrite array_count_transitions_spec_step by lia.
  destruct (Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0)); lia.
Qed. 

Lemma proof_of_array_count_transitions_entail_wit_2_2 : array_count_transitions_entail_wit_2_2.
Proof.
  unfold array_count_transitions_entail_wit_2_2.
  intros.
  entailer!.
  subst cnt.
  rewrite array_count_transitions_spec_step by lia.
  destruct (Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0)); lia.
Qed. 

Lemma proof_of_array_count_transitions_return_wit_1 : array_count_transitions_return_wit_1.
Proof.
  unfold array_count_transitions_return_wit_1.
  intros.
  entailer!.
  subst cnt.
  rewrite sublist_prefix_full by lia.
  reflexivity.
Qed. 
