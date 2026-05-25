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
From SimpleC.EE.CAV.verify_20260422_060249_array_min Require Import array_min_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_min_entail_wit_1 : array_min_entail_wit_1.
Proof.
  unfold array_min_entail_wit_1.
  intros.
  Exists 0.
  entailer!.
  intros j Hj.
  assert (j = 0) by lia.
  subst j.
  lia.
Qed.

Lemma proof_of_array_min_entail_wit_2_1 : array_min_entail_wit_2_1.
Proof.
  unfold array_min_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  intros j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j. lia.
  - assert (Hj_old : 0 <= j /\ j < i) by lia.
    specialize (H8 j Hj_old).
    lia.
Qed.
