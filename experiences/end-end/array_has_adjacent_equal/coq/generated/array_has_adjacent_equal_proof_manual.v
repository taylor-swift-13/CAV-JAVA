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
From SimpleC.EE.CAV.verify_20260422_045045_array_has_adjacent_equal Require Import array_has_adjacent_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_has_adjacent_equal_return_wit_2 : array_has_adjacent_equal_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  intros i [? ?].
  match goal with
  | H : forall j : Z, 1 <= j /\ j < _ -> _ |- _ =>
      apply H; lia
  end.
Qed.
