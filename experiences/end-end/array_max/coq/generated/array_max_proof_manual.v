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
From SimpleC.EE.CAV.verify_20260422_055419_array_max Require Import array_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Proof.
  unfold array_max_entail_wit_1.
  intros.
  Exists 0.
  entailer!.
  intros j Hj.
  assert (j = 0) by lia.
  subst j.
  lia.
Qed.

Lemma proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Proof.
  unfold array_max_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  intros j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j. lia.
  - assert (0 <= j /\ j < i) by lia.
    specialize (H6 j H9).
    lia.
Qed.
