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
From SimpleC.EE.CAV.verify_20260423_025651_string_has_double_char Require Import string_has_double_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_has_dup_char_entail_wit_1 : string_has_dup_char_entail_wit_1.
Proof.
  pre_process.
  assert (Hn_pos : 1 <= n).
  {
    assert (n <> 0).
    {
      intro Hn0.
      subst n.
      rewrite app_Znth2 in H by lia.
      replace (0 - Zlength l) with 0 in H by lia.
      simpl in H.
      contradiction.
    }
    lia.
  }
  entailer!.
Qed.

Lemma proof_of_string_has_dup_char_entail_wit_2 : string_has_dup_char_entail_wit_2.
Proof.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      contradiction.
  }
  entailer!.
  intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hj_lt | Hj_ge].
  - apply H5; lia.
  - assert (j = i) by lia.
    subst j.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    exact H.
Qed.

Lemma proof_of_string_has_dup_char_entail_wit_3 : string_has_dup_char_entail_wit_3.
Proof.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Znth i l 0 <> 0) as Hnz.
      {
        match goal with
        | Hnz_all : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz_all; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  entailer!.
Qed.

Lemma proof_of_string_has_dup_char_return_wit_1 : string_has_dup_char_return_wit_1.
Proof.
  pre_process.
  assert (Hn0 : n = 0).
  {
    destruct (Z_lt_ge_dec 0 n) as [Hpos | Hle].
    - assert (Znth 0 l 0 <> 0) as Hnz.
      {
        match goal with
        | Hnz_all : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz_all; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst n.
  Left.
  entailer!.
Qed.

Lemma proof_of_string_has_dup_char_return_wit_2 : string_has_dup_char_return_wit_2.
Proof.
  pre_process.
  assert (Hi_lt_n : i_3 < n).
  {
    destruct (Z_lt_ge_dec i_3 n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i_3 = n) by lia.
      subst i_3.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      contradiction.
  }
  Right.
  Exists i_3.
  entailer!.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  exact H.
Qed.
