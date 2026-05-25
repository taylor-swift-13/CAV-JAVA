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
From SimpleC.EE.CAV.verify_20260423_042409_string_starts_with Require Import string_starts_with_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_starts_with_return_wit_1 : string_starts_with_return_wit_1.
Proof.
  unfold string_starts_with_return_wit_1.
  pre_process.
  destruct (Z.eq_dec n 0) as [Hn_zero | Hn_nonzero].
  - subst n.
    assert (Hc_zero : c_pre = 0).
    {
      rewrite app_Znth2 in H by lia.
      replace (0 - Zlength l) with 0 in H by lia.
      change (Znth 0 (0 :: nil) 0) with 0 in H.
      lia.
    }
    Right.
    entailer!.
  - assert (Hn_pos : 0 < n) by lia.
    assert (Hhead_eq : Znth 0 l 0 = c_pre).
    {
      rewrite <- H.
      rewrite app_Znth1; lia.
    }
    Left.
    Left.
    Right.
    entailer!.
Qed.

Lemma proof_of_string_starts_with_return_wit_2 : string_starts_with_return_wit_2.
Proof.
  unfold string_starts_with_return_wit_2.
  pre_process.
  destruct (Z.eq_dec n 0) as [Hn_zero | Hn_nonzero].
  - subst n.
    assert (Hc_nonzero : c_pre <> 0).
    {
      intro Hc_zero.
      subst c_pre.
      rewrite app_Znth2 in H by lia.
      replace (0 - Zlength l) with 0 in H by lia.
      change (Znth 0 (0 :: nil) 0) with 0 in H.
      contradiction H; reflexivity.
    }
    Left.
    Right.
    entailer!.
  - assert (Hn_pos : 0 < n) by lia.
    assert (Hhead_ne : Znth 0 l 0 <> c_pre).
    {
      intro Hhead_eq.
      apply H.
      rewrite app_Znth1 by lia.
      exact Hhead_eq.
    }
    Left.
    Left.
    Left.
    entailer!.
Qed.
