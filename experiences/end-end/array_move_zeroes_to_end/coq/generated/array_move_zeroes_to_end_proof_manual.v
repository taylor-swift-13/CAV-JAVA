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
From SimpleC.EE.CAV.verify_20260422_061035_array_move_zeroes_to_end Require Import array_move_zeroes_to_end_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_move_zeroes_to_end.
Local Open Scope sac.
Import ListNotations.

Lemma amz_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros.
  revert i v.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl; reflexivity.
Qed.

Lemma amz_nth_replace_nth_eq:
  forall T (l: list T) i v u,
    (i < length l)%nat ->
    nth i (replace_nth i v l) u = v.
Proof.
  intros.
  revert i H.
  induction l; intros; simpl in *.
  - lia.
  - destruct i; simpl.
    + reflexivity.
    + apply IHl; lia.
Qed.

Lemma amz_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros.
  revert a b H.
  induction l; intros.
  - destruct a; destruct b; try lia; reflexivity.
  - destruct a0; simpl.
    + destruct b; simpl; [lia | reflexivity].
    + destruct b; simpl; try reflexivity.
      assert (a0 <> b)%nat by lia.
      apply IHl; easy.
Qed.

Lemma amz_replace_Znth_length {A: Type}:
  forall n (a: A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite amz_replace_nth_length.
  reflexivity.
Qed.

Lemma amz_Znth_replace_Znth_same :
  forall (n: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply amz_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma amz_Znth_replace_Znth_other :
  forall (n: Z) (m: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply amz_nth_replace_nth_other.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma amz_nonzero_snoc_nonzero :
  forall xs x,
    x <> 0 ->
    array_move_zeroes_to_end_nonzero (xs ++ [x]) =
    array_move_zeroes_to_end_nonzero xs ++ [x].
Proof.
  induction xs; intros x Hx; simpl.
  - destruct (Z.eq_dec x 0); [contradiction | reflexivity].
  - destruct (Z.eq_dec a 0); simpl; rewrite IHxs by exact Hx; reflexivity.
Qed.

Lemma amz_nonzero_snoc_zero :
  forall xs x,
    x = 0 ->
    array_move_zeroes_to_end_nonzero (xs ++ [x]) =
    array_move_zeroes_to_end_nonzero xs.
Proof.
  induction xs; intros x Hx; simpl.
  - subst x. destruct (Z.eq_dec 0 0); [reflexivity | contradiction].
  - destruct (Z.eq_dec a 0); simpl; rewrite IHxs by exact Hx; reflexivity.
Qed.

Lemma proof_of_array_move_zeroes_to_end_entail_wit_1 : array_move_zeroes_to_end_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_entail_wit_2_1 : array_move_zeroes_to_end_entail_wit_2_1.
Proof.
  pre_process.
  pose proof (H9 i ltac:(lia)) as Hi_l.
  assert (Hi_nonzero : Znth i l 0 <> 0) by congruence.
  assert (Hsnoc :
    sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]).
  {
    rewrite (sublist_split 0 (i + 1) i l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
    reflexivity.
  }
  assert (Hnz_next :
    array_move_zeroes_to_end_nonzero (sublist 0 (i + 1) l) =
    array_move_zeroes_to_end_nonzero (sublist 0 i l) ++ [Znth i l 0]).
  {
    rewrite Hsnoc.
    apply amz_nonzero_snoc_nonzero.
    exact Hi_nonzero.
  }
  Exists (replace_Znth write (Znth i lc_2 0) lc_2).
  entailer!.
  - intros k2 Hk2.
    rewrite amz_Znth_replace_Znth_other; try lia.
    apply H9; lia.
  - intros k Hk.
    rewrite Hnz_next.
    destruct (Z_lt_ge_dec k write) as [Hkw | Hkw].
    + rewrite amz_Znth_replace_Znth_other; try lia.
      rewrite app_Znth1 by (rewrite <- H7; lia).
      apply H8; lia.
    + assert (k = write) by lia.
      subst k.
      rewrite amz_Znth_replace_Znth_same by lia.
      rewrite Hi_l.
      rewrite app_Znth2 by (rewrite <- H7; lia).
      replace (write - Zlength (array_move_zeroes_to_end_nonzero (sublist 0 i l))) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
  - rewrite Hnz_next.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite amz_replace_Znth_length.
    exact H6.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_entail_wit_2_2 : array_move_zeroes_to_end_entail_wit_2_2.
Proof.
  pre_process.
  pose proof (H9 i ltac:(lia)) as Hi_l.
  assert (Hi_zero : Znth i l 0 = 0) by congruence.
  assert (Hsnoc :
    sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]).
  {
    rewrite (sublist_split 0 (i + 1) i l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
    reflexivity.
  }
  assert (Hnz_next :
    array_move_zeroes_to_end_nonzero (sublist 0 (i + 1) l) =
    array_move_zeroes_to_end_nonzero (sublist 0 i l)).
  {
    rewrite Hsnoc.
    apply amz_nonzero_snoc_zero.
    exact Hi_zero.
  }
  Exists lc_2.
  entailer!.
  - intros k2 Hk2.
    apply H9; lia.
  - intros k Hk.
    rewrite Hnz_next.
    apply H8; lia.
  - rewrite Hnz_next.
    exact H7.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_entail_wit_3 : array_move_zeroes_to_end_entail_wit_3.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hsub : sublist 0 n_pre l = l).
  {
    rewrite H4.
    apply sublist_self.
    reflexivity.
  }
  Exists lc.
  entailer!.
  - intros k Hk.
    rewrite Hsub in H6.
    lia.
  - intros k Hk.
    assert (Hkw : 0 <= k < write).
    { rewrite Hsub in H6. lia. }
    specialize (H7 k Hkw).
    rewrite Hsub in H7.
    exact H7.
  - rewrite Hsub in H6. lia.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_return_wit_1 : array_move_zeroes_to_end_return_wit_1.
Proof.
  pre_process.
  assert (Hzeros_len :
    forall xs,
      Zlength (array_move_zeroes_to_end_nonzero xs) +
      Zlength (array_move_zeroes_to_end_zeros xs) =
      Zlength xs).
  {
    induction xs; simpl.
    - rewrite !Zlength_nil. lia.
    - destruct (Z.eq_dec a 0); simpl; rewrite !Zlength_cons; lia.
  }
  assert (Hzero_value :
    forall xs k,
      Znth k (array_move_zeroes_to_end_zeros xs) 0 = 0).
  {
    induction xs; intros k; simpl.
    - unfold Znth. destruct (Z.to_nat k); reflexivity.
    - destruct (Z.eq_dec a 0) as [Ha | Ha].
      + subst a.
        destruct (Z_lt_ge_dec k 0) as [Hkneg | Hkge].
        * unfold Znth. replace (Z.to_nat k) with O by lia. reflexivity.
        * destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
          { subst k. rewrite Znth0_cons. reflexivity. }
          rewrite Znth_cons by lia.
          apply IHxs.
      + apply IHxs.
  }
  assert (Hwrite_end : write_2 = n_pre) by lia.
  subst write_2.
  assert (Hspec_len : Zlength (array_move_zeroes_to_end_spec l) = n_pre).
  {
    unfold array_move_zeroes_to_end_spec.
    rewrite Zlength_app.
    rewrite Hzeros_len.
    lia.
  }
  assert (Hlc_eq : lc_2 = array_move_zeroes_to_end_spec l).
  {
    apply (list_eq_ext 0).
    split.
    - lia.
    - intros k Hk.
      unfold array_move_zeroes_to_end_spec.
      destruct (Z_lt_ge_dec k (Zlength (array_move_zeroes_to_end_nonzero l))) as [Hkpre | Hksuf].
      + rewrite app_Znth1 by lia.
        apply H4; lia.
      + rewrite app_Znth2 by lia.
        rewrite H5 by lia.
        symmetry.
        apply Hzero_value.
  }
  subst lc_2.
  entailer!.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_which_implies_wit_1 : array_move_zeroes_to_end_which_implies_wit_1.
Proof.
  pre_process.
  assert (Hrange : 0 <= write < n_pre).
  { pose proof (Zlength_nonneg (array_move_zeroes_to_end_nonzero l)); lia. }
  sep_apply (IntArray.full_split_to_missing_i a write n_pre lc 0).
  - entailer!.
  - exact Hrange.
Qed. 

Lemma proof_of_array_move_zeroes_to_end_which_implies_wit_2 : array_move_zeroes_to_end_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hrange : 0 <= write < n_pre).
  { pose proof (Zlength_nonneg (array_move_zeroes_to_end_nonzero l)); lia. }
  sep_apply (IntArray.missing_i_merge_to_full).
  -
  Exists (replace_Znth write 0 lc).
  entailer!.
  + intros k Hk.
    destruct (Z.eq_dec k write) as [Hkeq | Hkneq].
    * subst k.
      rewrite amz_Znth_replace_Znth_same by lia.
      reflexivity.
    * assert (Hkrange : 0 <= k < Zlength lc).
      { pose proof (Zlength_nonneg (array_move_zeroes_to_end_nonzero l)); lia. }
      rewrite amz_Znth_replace_Znth_other by lia.
      apply H4; lia.
  + intros k Hk.
    assert (Hkrange : 0 <= k < Zlength lc).
    { pose proof (Zlength_nonneg (array_move_zeroes_to_end_nonzero l)); lia. }
    rewrite amz_Znth_replace_Znth_other by lia.
    apply H3; lia.
  + rewrite amz_replace_Znth_length.
    exact H2.
  - exact Hrange.
Qed. 
