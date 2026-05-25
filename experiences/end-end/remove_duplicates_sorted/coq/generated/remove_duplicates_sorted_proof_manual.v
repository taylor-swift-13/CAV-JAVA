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
From SimpleC.EE.CAV.verify_20260422_211833_remove_duplicates_sorted Require Import remove_duplicates_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import remove_duplicates_sorted.
Local Open Scope sac.
Import ListNotations.

Lemma list_eq_by_Znth :
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    (forall k, 0 <= k < Zlength l1 -> Znth k l1 0 = Znth k l2 0) ->
    l1 = l2.
Proof.
  intros l1.
  induction l1.
  - intros l2 Hlen _.
    rewrite Zlength_nil in Hlen.
    symmetry in Hlen.
    apply Zlength_nil_inv in Hlen.
    subst l2.
    reflexivity.
  - intros l2 Hlen Hnth.
    destruct l2.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg l1).
      lia.
    + f_equal.
      * assert (0 <= 0 < Zlength (a :: l1)).
        {
          rewrite Zlength_cons.
          pose proof (Zlength_nonneg l1).
          lia.
        }
        specialize (Hnth 0 H).
        simpl in Hnth.
        exact Hnth.
      * apply IHl1.
        -- rewrite !Zlength_cons in Hlen.
           lia.
        -- intros k Hk.
           assert (0 <= k + 1 < Zlength (a :: l1)).
           {
             rewrite Zlength_cons.
             pose proof (Zlength_nonneg l1).
             lia.
           }
           specialize (Hnth (k + 1) H).
           rewrite !Znth_cons in Hnth by lia.
           replace (k + 1 - 1) with k in Hnth by lia.
           exact Hnth.
Qed.

Lemma replace_nth_length:
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

Lemma nth_replace_nth_eq:
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

Lemma nth_a_replace_nth_b:
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

Lemma replace_Znth_length {A: Type}:
  forall n (a: A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros n a l.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length.
  reflexivity.
Qed.

Lemma Znth_replace_Znth_eq :
  forall (n: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma Znth_replace_Znth_other :
  forall (n: Z) (m: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply nth_a_replace_nth_b.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Fixpoint rds_last (prev : Z) (l : list Z) : Z :=
  match l with
  | nil => prev
  | x :: xs =>
      if Z.eq_dec x prev then rds_last prev xs else rds_last x xs
  end.

Lemma rds_from_snoc :
  forall prev xs x,
    remove_duplicates_sorted_cons prev (xs ++ [x]) =
    if Z.eq_dec x (rds_last prev xs) then
      remove_duplicates_sorted_cons prev xs
    else
      remove_duplicates_sorted_cons prev xs ++ [x].
Proof.
  intros prev xs.
  revert prev.
  induction xs; intros prev x; simpl.
  - destruct (Z.eq_dec x prev); reflexivity.
  - destruct (Z.eq_dec a prev); simpl.
    + apply IHxs.
    + rewrite IHxs.
      destruct (Z.eq_dec x (rds_last a xs)); reflexivity.
Qed.

Lemma rds_from_last_cons :
  forall prev xs,
    Znth (Zlength (prev :: remove_duplicates_sorted_cons prev xs) - 1)
      (prev :: remove_duplicates_sorted_cons prev xs) 0 =
    rds_last prev xs.
Proof.
  intros prev xs.
  revert prev.
  induction xs; intros prev; simpl.
  - reflexivity.
  - destruct (Z.eq_dec a prev).
    + specialize (IHxs prev).
      exact IHxs.
    + simpl.
      specialize (IHxs a).
      destruct (remove_duplicates_sorted_cons a xs) eqn:Ht.
      * simpl in IHxs.
        exact IHxs.
      * simpl in IHxs.
        rewrite !Zlength_cons in *.
        rewrite Znth_cons by (pose proof (Zlength_nonneg l); lia).
        replace (Z.succ (Z.succ (Z.succ (Zlength l))) - 1 - 1) with
          (Z.succ (Z.succ (Zlength l)) - 1) by lia.
        exact IHxs.
Qed.

Lemma rds_spec_snoc :
  forall p x,
    p <> nil ->
    remove_duplicates_sorted_spec (p ++ [x]) =
    if Z.eq_dec x
        (Znth (Zlength (remove_duplicates_sorted_spec p) - 1)
          (remove_duplicates_sorted_spec p) 0)
    then remove_duplicates_sorted_spec p
    else remove_duplicates_sorted_spec p ++ [x].
Proof.
  intros p x Hp.
  destruct p.
  - contradiction.
  - simpl.
    rewrite rds_from_snoc.
    rewrite rds_from_last_cons.
    destruct (Z.eq_dec x (rds_last z p)); reflexivity.
Qed.

Lemma rds_spec_singleton :
  forall x,
    remove_duplicates_sorted_spec [x] = [x].
Proof.
  intros; reflexivity.
Qed.

Lemma sublist_full_Zlength :
  forall (l : list Z),
    sublist 0 (Zlength l) l = l.
Proof.
  intros.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma proof_of_remove_duplicates_sorted_entail_wit_1 : remove_duplicates_sorted_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    replace (sublist 0 1 l) with [Znth 0 l 0]
      by (change (sublist 0 1 l) with (sublist 0 (0 + 1) l);
          rewrite (sublist_single 0 l 0) by (pose proof (Zlength_correct l); lia);
          reflexivity).
    reflexivity.
  - replace (sublist 0 1 l) with [Znth 0 l 0]
      by (change (sublist 0 1 l) with (sublist 0 (0 + 1) l);
          rewrite (sublist_single 0 l 0) by (pose proof (Zlength_correct l); lia);
          reflexivity).
    reflexivity.
Qed. 

Lemma proof_of_remove_duplicates_sorted_entail_wit_2_1 : remove_duplicates_sorted_entail_wit_2_1.
Proof.
  pre_process.
  pose proof (H8 i_2 ltac:(lia)) as Hi_l.
  pose proof (H7 (j_2 - 1) ltac:(lia)) as Hlast_lc.
  assert (Hneq_last :
    Znth i_2 l 0 <>
    Znth (Zlength (remove_duplicates_sorted_spec (sublist 0 i_2 l)) - 1)
      (remove_duplicates_sorted_spec (sublist 0 i_2 l)) 0).
  {
    rewrite <- H6.
    congruence.
  }
  assert (Hsnoc :
    sublist 0 (i_2 + 1) l =
    sublist 0 i_2 l ++ [Znth i_2 l 0]).
  {
    rewrite (sublist_split 0 (i_2 + 1) i_2 l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i_2 l 0) by (pose proof (Zlength_correct l); lia).
    reflexivity.
  }
  assert (Hspec_next :
    remove_duplicates_sorted_spec (sublist 0 (i_2 + 1) l) =
    remove_duplicates_sorted_spec (sublist 0 i_2 l) ++ [Znth i_2 l 0]).
  {
    rewrite Hsnoc.
    rewrite rds_spec_snoc.
    - destruct (Z.eq_dec (Znth i_2 l 0)
        (Znth (Zlength (remove_duplicates_sorted_spec (sublist 0 i_2 l)) - 1)
          (remove_duplicates_sorted_spec (sublist 0 i_2 l)) 0)).
      + contradiction.
      + reflexivity.
    - intro Hnil.
      assert (Zlength (sublist 0 i_2 l) = 0).
      { rewrite Hnil. rewrite Zlength_nil. reflexivity. }
      rewrite Zlength_sublist in H14 by lia.
      lia.
  }
  Exists (replace_Znth j_2 (Znth i_2 lc_2 0) lc_2).
  entailer!.
  - intros k2 Hk2.
    rewrite Znth_replace_Znth_other; try lia.
    apply H8; lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k j_2) as [Hkj | Hkj].
    + rewrite Znth_replace_Znth_other; try lia.
      rewrite Hspec_next.
      rewrite app_Znth1 by (rewrite <- H6; lia).
      apply H7; lia.
    + assert (k = j_2) by lia.
      subst k.
      rewrite Znth_replace_Znth_eq by lia.
      rewrite Hi_l.
      rewrite Hspec_next.
      rewrite app_Znth2 by (rewrite <- H6; lia).
      replace (j_2 - Zlength (remove_duplicates_sorted_spec (sublist 0 i_2 l))) with 0
        by lia.
      reflexivity.
  - rewrite Hspec_next.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite replace_Znth_length.
    exact H5.
Qed. 

Lemma proof_of_remove_duplicates_sorted_entail_wit_2_2 : remove_duplicates_sorted_entail_wit_2_2.
Proof.
  pre_process.
  pose proof (H8 i_2 ltac:(lia)) as Hi_l.
  pose proof (H7 (j_2 - 1) ltac:(lia)) as Hlast_lc.
  assert (Heq_last :
    Znth i_2 l 0 =
    Znth (Zlength (remove_duplicates_sorted_spec (sublist 0 i_2 l)) - 1)
      (remove_duplicates_sorted_spec (sublist 0 i_2 l)) 0).
  {
    rewrite <- H6.
    congruence.
  }
  assert (Hsnoc :
    sublist 0 (i_2 + 1) l =
    sublist 0 i_2 l ++ [Znth i_2 l 0]).
  {
    rewrite (sublist_split 0 (i_2 + 1) i_2 l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i_2 l 0) by (pose proof (Zlength_correct l); lia).
    reflexivity.
  }
  assert (Hspec_next :
    remove_duplicates_sorted_spec (sublist 0 (i_2 + 1) l) =
    remove_duplicates_sorted_spec (sublist 0 i_2 l)).
  {
    rewrite Hsnoc.
    rewrite rds_spec_snoc.
    - destruct (Z.eq_dec (Znth i_2 l 0)
        (Znth (Zlength (remove_duplicates_sorted_spec (sublist 0 i_2 l)) - 1)
          (remove_duplicates_sorted_spec (sublist 0 i_2 l)) 0)).
      + reflexivity.
      + contradiction.
    - intro Hnil.
      assert (Zlength (sublist 0 i_2 l) = 0).
      { rewrite Hnil. rewrite Zlength_nil. reflexivity. }
      rewrite Zlength_sublist in H14 by lia.
      lia.
  }
  Exists lc_2.
  entailer!.
  - intros k2 Hk2.
    apply H8; lia.
  - intros k Hk.
    rewrite Hspec_next.
    apply H7; lia.
  - rewrite Hspec_next.
    exact H6.
Qed. 

Lemma proof_of_remove_duplicates_sorted_return_wit_1 : remove_duplicates_sorted_return_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
  - rewrite H in H2.
    apply Zlength_nil_inv in H2.
    subst l.
    reflexivity.
  - rewrite H in H2.
    apply Zlength_nil_inv in H2.
    subst l.
    reflexivity.
Qed. 

Lemma proof_of_remove_duplicates_sorted_return_wit_2 : remove_duplicates_sorted_return_wit_2.
Proof.
  pre_process.
  assert (Hi_eq : i_2 = n_pre) by lia.
  subst i_2.
  assert (Hprefix_full : sublist 0 n_pre l = l).
  {
    replace n_pre with (Zlength l) by lia.
    apply sublist_full_Zlength.
  }
  rewrite Hprefix_full in H5, H6.
  Exists lc.
  entailer!.
  - apply list_eq_by_Znth.
    + assert (Hsub_len : Zlength (sublist 0 j lc) = j).
      {
        rewrite Zlength_sublist by lia.
        lia.
      }
      rewrite Hsub_len.
      lia.
    + intros k Hk.
      assert (Hsub_len : Zlength (sublist 0 j lc) = j).
      {
        rewrite Zlength_sublist by lia.
        lia.
      }
      rewrite Hsub_len in Hk.
      rewrite Znth_sublist by lia.
      replace (k + 0) with k by lia.
      apply H6; lia.
Qed. 
