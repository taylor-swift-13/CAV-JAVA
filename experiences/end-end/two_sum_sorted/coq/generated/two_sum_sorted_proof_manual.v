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
From SimpleC.EE.CAV.verify_20260423_052427_two_sum_sorted Require Import two_sum_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_two_sum_sorted_safety_wit_4 : two_sum_sorted_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - match goal with
    | Hrange: forall i j : Z, _ -> INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX |- _ =>
        pose proof (Hrange left right ltac:(lia)) as Hsum_range;
        lia
    end.
  - match goal with
    | Hrange: forall i j : Z, _ -> INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX |- _ =>
        pose proof (Hrange left right ltac:(lia)) as Hsum_range;
        lia
    end.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_1 : two_sum_sorted_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_two_sum_sorted_return_wit_2 : two_sum_sorted_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  intros i j Hij.
  destruct Hij as [[Hi0 Hij] Hjn].
  destruct (Z_lt_ge_dec i left) as [Hileft | Hlefti].
  - apply (H10 i j).
    lia.
  - apply (H11 i j).
    lia.
Qed.
