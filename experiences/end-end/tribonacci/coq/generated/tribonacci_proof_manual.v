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
From SimpleC.SL Require Import Mem SeparationLogic StoreAux.
From SimpleC.EE.CAV.verify_20260423_051744_tribonacci Require Import tribonacci_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import tribonacci.
Local Open Scope sac.

Ltac zcase x n :=
  let Heq := fresh "Heq" in
  let Hneq := fresh "Hneq" in
  destruct (Z.eq_dec x n) as [Heq | Hneq];
  [ subst; vm_compute; repeat split; try congruence; lia | idtac ].

Ltac split_tribonacci_range x :=
  zcase x 0; zcase x 1; zcase x 2; zcase x 3; zcase x 4;
  zcase x 5; zcase x 6; zcase x 7; zcase x 8; zcase x 9;
  zcase x 10; zcase x 11; zcase x 12; zcase x 13; zcase x 14;
  zcase x 15; zcase x 16; zcase x 17; zcase x 18; zcase x 19;
  zcase x 20; zcase x 21; zcase x 22; zcase x 23; zcase x 24;
  zcase x 25; zcase x 26; zcase x 27; zcase x 28; zcase x 29;
  zcase x 30; zcase x 31; zcase x 32; zcase x 33; zcase x 34;
  zcase x 35; zcase x 36; zcase x 37; lia.

Lemma tribonacci_z_sum_int_bound_3_37 :
  forall i,
    3 <= i ->
    i <= 37 ->
    INT_MIN <= (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) <= INT_MAX.
Proof.
  intros i Hlo Hhi.
  split_tribonacci_range i.
Qed.

Lemma tribonacci_z_pair_sum_int_bound_3_37 :
  forall i,
    3 <= i ->
    i <= 37 ->
    INT_MIN <= tribonacci_z (i - 3) + tribonacci_z (i - 2) <= INT_MAX.
Proof.
  intros i Hlo Hhi.
  split_tribonacci_range i.
Qed.

Lemma tribonacci_z_step_3_37 :
  forall i,
    3 <= i ->
    i <= 37 ->
    (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) = tribonacci_z i.
Proof.
  intros i Hlo Hhi.
  split_tribonacci_range i.
Qed.

Lemma proof_of_tribonacci_safety_wit_9 : tribonacci_safety_wit_9.
Proof.
  pre_process.
  entailer!; subst a; subst b; subst c;
    pose proof (tribonacci_z_sum_int_bound_3_37 i ltac:(lia) ltac:(lia)) as Htrib_bound;
    lia.
Qed.

Lemma proof_of_tribonacci_safety_wit_10 : tribonacci_safety_wit_10.
Proof.
  pre_process.
  entailer!; subst a; subst b;
    pose proof (tribonacci_z_pair_sum_int_bound_3_37 i ltac:(lia) ltac:(lia)) as Htrib_bound;
    lia.
Qed.

Lemma proof_of_tribonacci_entail_wit_1 : tribonacci_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_tribonacci_entail_wit_2 : tribonacci_entail_wit_2.
Proof.
  pre_process.
  entailer!; subst a; subst b; subst c.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - replace ((i + 1) - 1) with i by lia.
    apply tribonacci_z_step_3_37; lia.
  - replace ((i + 1) - 2) with (i - 1) by lia.
    reflexivity.
  - replace ((i + 1) - 3) with (i - 2) by lia.
    reflexivity.
Qed.

Lemma proof_of_tribonacci_return_wit_1 : tribonacci_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  vm_compute.
  lia.
Qed.

Lemma proof_of_tribonacci_return_wit_2 : tribonacci_return_wit_2.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  vm_compute.
  lia.
Qed.
