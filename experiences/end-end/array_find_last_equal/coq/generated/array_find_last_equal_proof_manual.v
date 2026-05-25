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
From SimpleC.EE.CAV.verify_20260422_040059_array_find_last_equal Require Import array_find_last_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_find_last_equal_entail_wit_1 : array_find_last_equal_entail_wit_1.
Proof.
  unfold array_find_last_equal_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_array_find_last_equal_entail_wit_2_1 : array_find_last_equal_entail_wit_2_1.
Proof.
  unfold array_find_last_equal_entail_wit_2_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_array_find_last_equal_entail_wit_3 : array_find_last_equal_entail_wit_3.
Proof.
  unfold array_find_last_equal_entail_wit_3.
  intros.
  entailer!.
  - intros Hans_nonneg.
    assert (Hi_eq : i = n_pre) by lia.
    destruct (H7 Hans_nonneg) as [Hans_val Hlast].
    split.
    + exact Hans_val.
    + intros j Hj.
      apply Hlast.
      lia.
  - intros Hans_eq j Hj.
    assert (Hi_eq : i = n_pre) by lia.
    pose proof (H6 Hans_eq) as Hnone.
    apply Hnone.
    lia.
Qed. 

Lemma proof_of_array_find_last_equal_return_wit_1 : array_find_last_equal_return_wit_1.
Proof.
  unfold array_find_last_equal_return_wit_1.
  pre_process.
  destruct (Z.eq_dec ans (-1)) as [Hans_eq | Hans_neq].
  - Right.
    entailer!.
  - assert (Hans_nonneg : 0 <= ans) by lia.
    destruct (H4 Hans_nonneg) as [Hans_val Hlast].
    Left.
    entailer!.
Qed. 
