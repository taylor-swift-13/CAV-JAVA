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
From SimpleC.EE.CAV.verify_20260422_222714_string_all_digits Require Import string_all_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_all_digits.
Local Open Scope sac.

Lemma string_all_digits_spec_app_digit :
  forall (l : list Z) (x : Z),
    string_all_digits_spec l = 1 ->
    x >= 48 /\ x <= 57 ->
    string_all_digits_spec (l ++ x :: nil) = 1.
Proof.
  induction l; intros x Hspec Hrange.
  - simpl.
    destruct (Z_lt_dec x 48) as [Hx_lt | Hx_nlt].
    + lia.
    + destruct (Z_gt_dec x 57) as [Hx_gt | Hx_ngt].
      * lia.
      * reflexivity.
  - simpl in Hspec.
    destruct (Z_lt_dec a 48) as [Ha_lt | Ha_nlt].
    + discriminate.
    + destruct (Z_gt_dec a 57) as [Ha_gt | Ha_ngt].
      * discriminate.
      * simpl.
        destruct (Z_lt_dec a 48) as [Ha_lt' | Ha_nlt'].
        -- lia.
        -- destruct (Z_gt_dec a 57) as [Ha_gt' | Ha_ngt'].
           ++ lia.
           ++ apply IHl; [exact Hspec | exact Hrange].
Qed.

Lemma string_all_digits_spec_app_bad_high :
  forall (l1 l2 : list Z) (x : Z),
    string_all_digits_spec l1 = 1 ->
    x > 57 ->
    string_all_digits_spec (l1 ++ x :: l2) = 0.
Proof.
  induction l1; intros l2 x Hspec Hgt.
  - simpl.
    destruct (Z_lt_dec x 48) as [Hx_lt | Hx_nlt].
    + lia.
    + destruct (Z_gt_dec x 57) as [Hx_gt | Hx_ngt].
      * reflexivity.
      * lia.
  - simpl in Hspec.
    destruct (Z_lt_dec a 48) as [Ha_lt | Ha_nlt].
    + discriminate.
    + destruct (Z_gt_dec a 57) as [Ha_gt | Ha_ngt].
      * discriminate.
      * simpl.
        destruct (Z_lt_dec a 48) as [Ha_lt' | Ha_nlt'].
        -- lia.
        -- destruct (Z_gt_dec a 57) as [Ha_gt' | Ha_ngt'].
           ++ lia.
           ++ apply IHl1; [exact Hspec | exact Hgt].
Qed.

Lemma string_all_digits_spec_app_bad_low :
  forall (l1 l2 : list Z) (x : Z),
    string_all_digits_spec l1 = 1 ->
    x < 48 ->
    string_all_digits_spec (l1 ++ x :: l2) = 0.
Proof.
  induction l1; intros l2 x Hspec Hlt.
  - simpl.
    destruct (Z_lt_dec x 48); [reflexivity | lia].
  - simpl in Hspec.
    destruct (Z_lt_dec a 48) as [Ha_lt | Ha_nlt].
    + discriminate.
    + destruct (Z_gt_dec a 57) as [Ha_gt | Ha_ngt].
      * discriminate.
      * simpl.
        destruct (Z_lt_dec a 48) as [Ha_lt' | Ha_nlt'].
        -- lia.
        -- destruct (Z_gt_dec a 57) as [Ha_gt' | Ha_ngt'].
           ++ lia.
           ++ apply IHl1; [exact Hspec | exact Hlt].
Qed.

Lemma proof_of_string_all_digits_entail_wit_1 : string_all_digits_entail_wit_1.
Proof.
  unfold string_all_digits_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_all_digits_entail_wit_2 : string_all_digits_entail_wit_2.
Proof.
  unfold string_all_digits_entail_wit_2.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  rewrite H4 in *.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      destruct l2_2.
      + rewrite app_nil_r in H1.
        rewrite app_Znth2 in H1 by lia.
        replace (Zlength l1_2 - Zlength l1_2) with 0 in H1 by lia.
        simpl in H1.
        contradiction.
      + exfalso.
        rename z into x0.
        rename l2_2 into xs0.
        rewrite Zlength_app, Zlength_cons in Hlen_l.
        pose proof Zlength_nonneg xs0.
        lia.
  }
  destruct l2_2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1.
    contradiction.
  - rename z into x.
    rename l2_2 into xs.
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + assert (Hx_digit : x >= 48 /\ x <= 57).
      {
        split.
        * rewrite <- app_assoc in H0.
          rewrite app_Znth2 in H0 by lia.
          replace (i - Zlength l1_2) with 0 in H0 by lia.
          change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H0.
          exact H0.
        * rewrite <- app_assoc in H.
          rewrite app_Znth2 in H by lia.
          replace (i - Zlength l1_2) with 0 in H by lia.
          change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H.
          exact H.
      }
      apply string_all_digits_spec_app_digit; [exact H6 | exact Hx_digit].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_string_all_digits_return_wit_1 : string_all_digits_return_wit_1.
Proof.
  unfold string_all_digits_return_wit_1.
  pre_process.
  entailer!.
  rewrite H4 in *.
  destruct l2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1) with 0 in H1 by lia.
    simpl in H1.
    contradiction.
  - rename z into x.
    rename l2 into xs.
    assert (Hx_gt : x > 57).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1) with 0 in H by lia.
      simpl in H.
      exact H.
    }
    symmetry.
    apply string_all_digits_spec_app_bad_high with (l1 := l1) (l2 := xs).
    + exact H6.
    + exact Hx_gt.
Qed.

Lemma proof_of_string_all_digits_return_wit_2 : string_all_digits_return_wit_2.
Proof.
  unfold string_all_digits_return_wit_2.
  pre_process.
  entailer!.
  rewrite H3 in *.
  destruct l2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1) with 0 in H0 by lia.
    simpl in H0.
    contradiction.
  - rename z into x.
    rename l2 into xs.
    assert (Hx_lt : x < 48).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1) with 0 in H by lia.
      simpl in H.
      exact H.
    }
    symmetry.
    apply string_all_digits_spec_app_bad_low with (l1 := l1) (l2 := xs).
    + exact H5.
    + exact Hx_lt.
Qed.

Lemma proof_of_string_all_digits_return_wit_3 : string_all_digits_return_wit_3.
Proof.
  unfold string_all_digits_return_wit_3.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Hnz_i : Znth i l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  entailer!.
  destruct l2.
  - rewrite H2.
    rewrite app_nil_r.
    symmetry.
    exact H4.
  - rename z into x.
    rename l2 into xs.
    exfalso.
    rewrite H2 in Hlen_l.
    rewrite Zlength_app, Zlength_cons in Hlen_l.
    pose proof Zlength_nonneg xs.
    lia.
Qed.
