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
From SimpleC.EE.CAV.verify_20260422_205655_power_nonnegative Require Import power_nonnegative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import power_nonnegative.
Local Open Scope sac.

Lemma power_nonnegative_z_succ:
  forall base i,
    0 <= i ->
    power_nonnegative_z base (i + 1) =
    power_nonnegative_z base i * base.
Proof.
  intros base i Hi.
  unfold power_nonnegative_z.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_power_nonnegative_safety_wit_3 : power_nonnegative_safety_wit_3.
Proof.
  pre_process.
  rewrite <- power_nonnegative_z_succ by lia.
  entailer!.
  - pose proof (H9 (i + 1) ltac:(lia)) as Hbound.
    lia.
  - pose proof (H9 (i + 1) ltac:(lia)) as Hbound.
    lia.
Qed.

Lemma proof_of_power_nonnegative_entail_wit_1 : power_nonnegative_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_power_nonnegative_entail_wit_3 : power_nonnegative_entail_wit_3.
Proof.
  pre_process.
  rewrite <- power_nonnegative_z_succ by lia.
  entailer!.
Qed.
