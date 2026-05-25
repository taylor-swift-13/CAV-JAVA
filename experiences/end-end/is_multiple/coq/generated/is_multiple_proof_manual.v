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
From SimpleC.EE.CAV.verify_20260422_175633_is_multiple Require Import is_multiple_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_is_multiple_return_wit_1 : is_multiple_return_wit_1.
Proof.
  pre_process.
  Right.
  assert (Hb_nonzero: b_pre <> 0) by lia.
  destruct (Z.rem_divide a_pre b_pre Hb_nonzero) as [Hrem_to_div _].
  pose proof (Hrem_to_div H) as [q Hq].
  Exists q.
  rewrite Z.mul_comm.
  rewrite Hq.
  entailer!.
Qed.

Lemma proof_of_is_multiple_return_wit_2 : is_multiple_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  intros q Hmultiple.
  apply H.
  rewrite Hmultiple.
  apply Z.rem_mul.
  lia.
Qed.
