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
From SimpleC.EE.CAV.verify_20260423_044027_string_to_lower_ascii Require Import string_to_lower_ascii_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_to_lower_ascii_entail_wit_1 : string_to_lower_ascii_entail_wit_1.
Proof.
  pre_process.
  Exists (l ++ 0 :: nil) (@nil Z).
  entailer!.
  - replace (n - 0) with (Zlength l) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    simpl. reflexivity.
  - intros t Ht.
    replace (0 + t) with t by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 
