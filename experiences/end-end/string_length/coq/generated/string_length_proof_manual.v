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
From SimpleC.EE.CAV.verify_20260423_121011_string_length Require Import string_length_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_length_entail_wit_2 : string_length_entail_wit_2.
Proof.
  unfold string_length_entail_wit_2.
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
  entailer!.
Qed. 

Lemma proof_of_string_length_entail_wit_3 : string_length_entail_wit_3.
Proof.
  unfold string_length_entail_wit_3.
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
