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
From SimpleC.EE.CAV.verify_20260422_131939_climb_stairs Require Import climb_stairs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import climb_stairs.
Local Open Scope sac.

Ltac zcase x n :=
  let Heq := fresh "Heq" in
  let Hneq := fresh "Hneq" in
  destruct (Z.eq_dec x n) as [Heq | Hneq];
  [ subst; vm_compute; repeat split; try congruence; lia | idtac ].

Ltac split_small_range x :=
  zcase x 0; zcase x 1; zcase x 2; zcase x 3; zcase x 4;
  zcase x 5; zcase x 6; zcase x 7; zcase x 8; zcase x 9;
  zcase x 10; zcase x 11; zcase x 12; zcase x 13; zcase x 14;
  zcase x 15; zcase x 16; zcase x 17; zcase x 18; zcase x 19;
  zcase x 20; zcase x 21; zcase x 22; zcase x 23; zcase x 24;
  zcase x 25; zcase x 26; zcase x 27; zcase x 28; zcase x 29;
  zcase x 30; zcase x 31; zcase x 32; zcase x 33; zcase x 34;
  zcase x 35; zcase x 36; zcase x 37; zcase x 38; zcase x 39;
  zcase x 40; zcase x 41; zcase x 42; zcase x 43; zcase x 44;
  zcase x 45; lia.

Lemma proof_of_climb_stairs_safety_wit_7 : climb_stairs_safety_wit_7.
Proof.
  pre_process.
  entailer!; subst prev1; subst prev2; split_small_range i.
Qed.

Lemma proof_of_climb_stairs_entail_wit_1 : climb_stairs_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_climb_stairs_entail_wit_2 : climb_stairs_entail_wit_2.
Proof.
  pre_process.
  entailer!; subst prev1; subst prev2; split_small_range i.
Qed.

Lemma proof_of_climb_stairs_return_wit_1 : climb_stairs_return_wit_1.
Proof.
  pre_process.
  entailer!.
  split_small_range n_pre.
Qed.
