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
From SimpleC.EE.CAV.verify_20260423_024227_string_find_char Require Import string_find_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_find_char_entail_wit_2 : string_find_char_entail_wit_2.
Proof.
  unfold string_find_char_entail_wit_2.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq_n : i = n) by lia.
      subst i.
      match goal with
      | Hnz : Znth n (l ++ 0 :: nil) 0 <> 0,
        Hlen : Zlength l = n |- _ =>
          rewrite app_Znth2 in Hnz by lia;
          replace (n - Zlength l) with 0 in Hnz by lia;
          simpl in Hnz;
          contradiction
      end.
  }
  assert (Hi_neq_c : Znth i l 0 <> c_pre).
  {
    match goal with
    | Hneq : Znth i (l ++ 0 :: nil) 0 <> c_pre |- _ =>
        rewrite app_Znth1 in Hneq by lia;
        exact Hneq
    end.
  }
  entailer!.
  intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hjlt | Hjge].
  - match goal with
    | Hpref : forall j : Z, 0 <= j < i -> Znth j l 0 <> c_pre |- _ =>
        apply Hpref; lia
    end.
  - assert (j = i) by lia.
    subst j.
    exact Hi_neq_c.
Qed. 

Lemma proof_of_string_find_char_entail_wit_3 : string_find_char_entail_wit_3.
Proof.
  unfold string_find_char_entail_wit_3.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Hi_nonzero : Znth i l 0 <> 0).
      {
        match goal with
        | Hnz_all : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz_all; lia
        end.
      }
      match goal with
      | Hz : Znth i (l ++ 0 :: nil) 0 = 0 |- _ =>
          rewrite app_Znth1 in Hz by lia;
          contradiction
      end.
    - lia.
  }
  subst i.
  entailer!.
Qed. 

Lemma proof_of_string_find_char_return_wit_1 : string_find_char_return_wit_1.
Proof.
  unfold string_find_char_return_wit_1.
  pre_process.
  assert (Hi_lt_n : i_2 < n).
  {
    destruct (Z_lt_ge_dec i_2 n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq_n : i_2 = n) by lia.
      subst i_2.
      match goal with
      | Hnz : Znth n (l ++ 0 :: nil) 0 <> 0,
        Hlen : Zlength l = n |- _ =>
          rewrite app_Znth2 in Hnz by lia;
          replace (n - Zlength l) with 0 in Hnz by lia;
          simpl in Hnz;
          contradiction
      end.
  }
  assert (Hi_eq_c : Znth i_2 l 0 = c_pre).
  {
    match goal with
    | Heq : Znth i_2 (l ++ 0 :: nil) 0 = c_pre |- _ =>
        rewrite app_Znth1 in Heq by lia;
        exact Heq
    end.
  }
  Left.
  entailer!.
Qed. 
