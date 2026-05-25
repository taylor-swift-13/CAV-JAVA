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
From SimpleC.EE.CAV.verify_20260423_004841_string_count_lowercase Require Import string_count_lowercase_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_lowercase.
Local Open Scope sac.

Lemma string_count_lowercase_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_lowercase_spec (l ++ x :: nil) =
    string_count_lowercase_spec l +
    (if Z_le_dec 97 x then if Z_le_dec x 122 then 1 else 0 else 0).
Proof.
  induction l; intros x.
  - simpl. destruct (Z_le_dec 97 x); destruct (Z_le_dec x 122); lia.
  - simpl.
    destruct (Z_le_dec 97 a);
      destruct (Z_le_dec a 122);
      rewrite IHl;
      destruct (Z_le_dec 97 x);
      destruct (Z_le_dec x 122);
      lia.
Qed.

Lemma proof_of_string_count_lowercase_entail_wit_1 : string_count_lowercase_entail_wit_1.
Proof.
  unfold string_count_lowercase_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_count_lowercase_entail_wit_2_1 : string_count_lowercase_entail_wit_2_1.
Proof.
  unfold string_count_lowercase_entail_wit_2_1.
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
      rewrite Hi_eq in H1.
      rewrite app_Znth2 in H1 by lia.
      replace (n - Zlength l) with 0 in H1 by lia.
      simpl in H1.
      exfalso.
      apply H1.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1.
    exfalso.
    apply H1.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_ge : 97 <= x).
    {
      rewrite <- app_assoc in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (i - Zlength l1_2) with 0 in H0 by lia.
      simpl in H0.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H0.
      lia.
    }
    assert (Hx_le : x <= 122).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      lia.
    }
    assert (Hspec_next :
      cnt + 1 = string_count_lowercase_spec (l1_2 ++ x :: nil)).
    {
      subst cnt.
      rewrite string_count_lowercase_spec_app_single.
      destruct (Z_le_dec 97 x); destruct (Z_le_dec x 122); lia.
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

Lemma proof_of_string_count_lowercase_entail_wit_2_2 : string_count_lowercase_entail_wit_2_2.
Proof.
  unfold string_count_lowercase_entail_wit_2_2.
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
    assert (Hx_lt : x < 97).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      lia.
    }
    assert (Hspec_next :
      cnt = string_count_lowercase_spec (l1_2 ++ x :: nil)).
    {
      subst cnt.
      rewrite string_count_lowercase_spec_app_single.
      destruct (Z_le_dec 97 x); destruct (Z_le_dec x 122); lia.
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

Lemma proof_of_string_count_lowercase_entail_wit_2_3 : string_count_lowercase_entail_wit_2_3.
Proof.
  unfold string_count_lowercase_entail_wit_2_3.
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
      rewrite Hi_eq in H1.
      rewrite app_Znth2 in H1 by lia.
      replace (n - Zlength l) with 0 in H1 by lia.
      simpl in H1.
      exfalso.
      apply H1.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1.
    exfalso.
    apply H1.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_gt : x > 122).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      lia.
    }
    assert (Hspec_next :
      cnt = string_count_lowercase_spec (l1_2 ++ x :: nil)).
    {
      subst cnt.
      rewrite string_count_lowercase_spec_app_single.
      destruct (Z_le_dec 97 x); destruct (Z_le_dec x 122); lia.
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

Lemma proof_of_string_count_lowercase_entail_wit_3 : string_count_lowercase_entail_wit_3.
Proof.
  unfold string_count_lowercase_entail_wit_3.
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
      rewrite app_Znth1 in H by lia.
      contradiction.
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
  assert (Hspec_full : cnt = string_count_lowercase_spec l).
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
