Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260423_030819_string_is_empty Require Import string_is_empty_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_is_empty_return_wit_1 : string_is_empty_return_wit_1.
Proof.
  pre_process.
  assert (n = 0) as Hn.
  {
    destruct (Z.eq_dec n 0) as [Hz | Hnz].
    - exact Hz.
    - assert (0 < n) as Hpos by lia.
      assert (Znth 0 l 0 <> 0) as Hnonzero by (apply H3; lia).
      assert (Znth 0 (l ++ 0 :: nil) 0 = Znth 0 l 0) as Happ.
      { rewrite app_Znth1; lia. }
      congruence.
  }
  Right.
  entailer!.
Qed.

Lemma proof_of_string_is_empty_return_wit_2 : string_is_empty_return_wit_2.
Proof.
  pre_process.
  assert (0 < n) as Hn.
  {
    destruct (Z.eq_dec n 0) as [Hz | Hnz].
    - exfalso.
      subst n.
      rewrite app_Znth2 in H by lia.
      simpl in H.
      rewrite Hz in H.
      simpl in H.
      contradiction.
    - lia.
  }
  Left.
  entailer!.
Qed.
