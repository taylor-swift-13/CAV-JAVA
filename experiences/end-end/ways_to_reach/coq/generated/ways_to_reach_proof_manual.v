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
From SimpleC.EE.CAV.verify_20260423_054104_ways_to_reach Require Import ways_to_reach_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import ways_to_reach.
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

Lemma ways_to_reach_nat_step : forall n,
  ways_to_reach_nat (S (S n)) = ways_to_reach_nat (S n) + ways_to_reach_nat n.
Proof.
  intros n. unfold ways_to_reach_nat. simpl.
  destruct (ways_to_reach_pair n) as [x y]. simpl. lia.
Qed.

Lemma ways_to_reach_z_step : forall z,
  2 <= z -> ways_to_reach_z z = ways_to_reach_z (z - 1) + ways_to_reach_z (z - 2).
Proof.
  intros z Hz.
  unfold ways_to_reach_z.
  set (k := z - 2).
  assert (Hk : 0 <= k) by (subst k; lia).
  assert (Hz0 : z = k + 2) by (subst k; lia).
  assert (Hz1 : z - 1 = k + 1) by (subst k; lia).
  rewrite Hz1, Hz0.
  rewrite !Z2Nat.inj_add by lia.
  change (Z.to_nat 2) with 2%nat.
  change (Z.to_nat 1) with 1%nat.
  replace (Z.to_nat k + 2)%nat with (S (S (Z.to_nat k))) by lia.
  replace (Z.to_nat k + 1)%nat with (S (Z.to_nat k)) by lia.
  apply ways_to_reach_nat_step.
Qed.

Lemma ways_to_reach_z_bound_45 : forall z,
  0 <= z <= 45 -> 0 <= ways_to_reach_z z <= INT_MAX.
Proof.
  intros z Hz.
  split_small_range z.
Qed.

Lemma proof_of_ways_to_reach_safety_wit_6 : ways_to_reach_safety_wit_6.
Proof.
  pre_process.
  entailer!; subst a; subst b.
  - replace (ways_to_reach_z (i - 2) + ways_to_reach_z (i - 1))
      with (ways_to_reach_z (i - 1) + ways_to_reach_z (i - 2)) by lia.
    rewrite <- ways_to_reach_z_step by lia.
    pose proof (ways_to_reach_z_bound_45 i ltac:(lia)).
    lia.
  - replace (ways_to_reach_z (i - 2) + ways_to_reach_z (i - 1))
      with (ways_to_reach_z (i - 1) + ways_to_reach_z (i - 2)) by lia.
    rewrite <- ways_to_reach_z_step by lia.
    pose proof (ways_to_reach_z_bound_45 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_ways_to_reach_entail_wit_1 : ways_to_reach_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_ways_to_reach_entail_wit_2 : ways_to_reach_entail_wit_2.
Proof.
  pre_process.
  sep_apply (poly_store_poly_undef_store (&( "c")) FET_int (a + b)).
  entailer!; subst a; subst b.
  - replace (i + 1 - 1) with i by lia.
    rewrite (ways_to_reach_z_step i H2).
    lia.
  - replace (i + 1 - 2) with (i - 1) by lia.
    reflexivity.
Qed.

Lemma proof_of_ways_to_reach_return_wit_1 : ways_to_reach_return_wit_1.
Proof.
  pre_process.
  entailer!; subst n_pre; vm_compute; repeat split; try congruence; lia.
Qed.
