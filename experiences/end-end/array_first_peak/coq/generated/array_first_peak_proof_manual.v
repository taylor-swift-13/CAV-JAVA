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
From SimpleC.EE.CAV.verify_20260422_042345_array_first_peak Require Import array_first_peak_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  intros j [? ?].
  match goal with
  | Hprefix : forall k : Z, 0 < k /\ k < i -> _ |- _ =>
      apply Hprefix
  end.
  lia.
Qed.

Lemma proof_of_array_first_peak_return_wit_2 : array_first_peak_return_wit_2.
Proof.
  pre_process.
  entailer!.
  Right.
  entailer!.
Qed.
