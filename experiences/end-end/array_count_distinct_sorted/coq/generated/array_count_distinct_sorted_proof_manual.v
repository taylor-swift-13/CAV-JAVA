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
From SimpleC.EE.CAV.verify_20260422_030111_array_count_distinct_sorted Require Import array_count_distinct_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_distinct_sorted.
Local Open Scope sac.

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

Lemma array_count_distinct_sorted_from_snoc :
  forall (prev y : Z) (xs : list Z),
    array_count_distinct_sorted_from prev (xs ++ (y :: nil)) =
    array_count_distinct_sorted_from prev xs +
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

Lemma array_count_distinct_sorted_spec_snoc_nonempty :
  forall (xs : list Z) (y d : Z),
    xs <> nil ->
    array_count_distinct_sorted_spec (xs ++ (y :: nil)) =
    array_count_distinct_sorted_spec xs +
    (if Z.eq_dec y (last xs d) then 0 else 1).
Proof.
  intros xs y d Hnonempty.
  destruct xs.
  - contradiction.
  - simpl.
    rewrite array_count_distinct_sorted_from_snoc.
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

Lemma proof_of_array_count_distinct_sorted_entail_wit_1 : array_count_distinct_sorted_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (Hn_pos : 1 <= n_pre) by lia.
  replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
  - simpl. reflexivity.
  - rewrite <- (sublist_single 0 l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
Qed.

Lemma proof_of_array_count_distinct_sorted_entail_wit_2_1 : array_count_distinct_sorted_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  rewrite H5.
  rewrite sublist_prefix_snoc_Z by lia.
  rewrite array_count_distinct_sorted_spec_snoc_nonempty with (d := 0).
  - rewrite last_sublist_prefix_Z by lia.
    destruct (Z.eq_dec (Znth i_2 l 0) (Znth (i_2 - 1) l 0)); lia.
  - apply sublist_prefix_nonempty_Z; lia.
Qed.

Lemma proof_of_array_count_distinct_sorted_entail_wit_2_2 : array_count_distinct_sorted_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  rewrite H5.
  rewrite sublist_prefix_snoc_Z by lia.
  rewrite array_count_distinct_sorted_spec_snoc_nonempty with (d := 0).
  - rewrite last_sublist_prefix_Z by lia.
    destruct (Z.eq_dec (Znth i_2 l 0) (Znth (i_2 - 1) l 0)); lia.
  - apply sublist_prefix_nonempty_Z; lia.
Qed.

Lemma proof_of_array_count_distinct_sorted_return_wit_1 : array_count_distinct_sorted_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  apply Zlength_nil_inv in H2.
  subst l.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_array_count_distinct_sorted_return_wit_2 : array_count_distinct_sorted_return_wit_2.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq : i_2 = n_pre) by lia.
  subst i_2.
  rewrite H4.
  rewrite (sublist_self l n_pre) by (symmetry; exact H8).
  reflexivity.
Qed.
