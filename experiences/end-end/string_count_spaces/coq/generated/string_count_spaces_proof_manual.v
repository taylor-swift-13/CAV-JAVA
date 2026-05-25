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
From SimpleC.EE.CAV.verify_20260423_011517_string_count_spaces Require Import string_count_spaces_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_spaces.
Local Open Scope sac.

Lemma string_count_spaces_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_spaces_spec (l ++ x :: nil) =
    string_count_spaces_spec l + (if Z.eq_dec x 32 then 1 else 0).
Proof.
  induction l; intros x.
  - simpl. destruct (Z.eq_dec x 32); lia.
  - simpl.
    destruct (Z.eq_dec a 32);
      rewrite IHl;
      destruct (Z.eq_dec x 32);
      lia.
Qed.

Lemma proof_of_string_count_spaces_entail_wit_1 : string_count_spaces_entail_wit_1.
Proof.
  unfold string_count_spaces_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_count_spaces_entail_wit_2_1 : string_count_spaces_entail_wit_2_1.
Proof.
  unfold string_count_spaces_entail_wit_2_1.
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
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_eq : x = 32).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      lia.
    }
    assert (Hspec_next :
      cnt + 1 = string_count_spaces_spec (l1_2 ++ x :: nil)).
    {
      subst cnt.
      rewrite string_count_spaces_spec_app_single.
      destruct (Z.eq_dec x 32); lia.
    }
    assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs).
    {
      rewrite <- app_assoc.
      reflexivity.
    }
    assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1).
    {
      rewrite Zlength_app_cons.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
Qed.

Lemma proof_of_string_count_spaces_entail_wit_2_2 : string_count_spaces_entail_wit_2_2.
Proof.
  unfold string_count_spaces_entail_wit_2_2.
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
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_ne : x <> 32).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      exact H.
    }
    assert (Hspec_next :
      cnt = string_count_spaces_spec (l1_2 ++ x :: nil)).
    {
      subst cnt.
      rewrite string_count_spaces_spec_app_single.
      destruct (Z.eq_dec x 32); lia.
    }
    assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs).
    {
      rewrite <- app_assoc.
      reflexivity.
    }
    assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1).
    {
      rewrite Zlength_app_cons.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
Qed.

Lemma proof_of_string_count_spaces_entail_wit_3 : string_count_spaces_entail_wit_3.
Proof.
  unfold string_count_spaces_entail_wit_3.
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
    - assert (Znth i l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
      }
      match goal with
      | Hzero : Znth i (l ++ 0 :: nil) 0 = 0 |- _ =>
          rewrite app_Znth1 in Hzero by lia;
          contradiction
      end.
    - lia.
  }
  subst i.
  assert (Hl1_eq_l : l1_2 = l).
  {
    subst l.
    destruct l2_2.
    - rewrite app_nil_r.
      reflexivity.
    - rename z into x.
      rename l2_2 into xs.
      exfalso.
      rewrite Zlength_app, Zlength_cons in Hlen_l.
      pose proof Zlength_nonneg xs.
      lia.
  }
  assert (Hspec_full : cnt = string_count_spaces_spec l).
  {
    subst cnt.
    rewrite Hl1_eq_l.
    reflexivity.
  }
  replace (Zlength l1_2) with n by lia.
  Exists l.
  Exists nil.
  entailer!; try rewrite app_nil_r; try reflexivity.
Qed.
