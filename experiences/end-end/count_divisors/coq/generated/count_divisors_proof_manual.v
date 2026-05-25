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
From SimpleC.EE.CAV.verify_20260422_145616_count_divisors Require Import count_divisors_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_divisors.
Require Import count_divisors_helper.
Local Open Scope sac.

Lemma count_divisors_upto_z_zero :
  forall n, count_divisors_upto_z n 0 = 0.
Proof.
  intros n.
  unfold count_divisors_upto_z.
  simpl.
  reflexivity.
Qed.

Lemma count_divisors_upto_z_step_divides :
  forall n d,
    1 <= d ->
    n % (d) = 0 ->
    count_divisors_upto_z n d =
      count_divisors_upto_z n (d - 1) + 1.
Proof.
  intros n d Hd Hmod.
  unfold count_divisors_upto_z.
  replace (Z.to_nat d) with (S (Z.to_nat (d - 1))) by lia.
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) with d by lia.
  destruct (Z.eq_dec (Z.rem n d) 0) as [Hrem | Hrem].
  - reflexivity.
  - exfalso.
    apply Hrem.
    exact Hmod.
Qed.

Lemma count_divisors_upto_z_step_not_divides :
  forall n d,
    1 <= d ->
    n % (d) <> 0 ->
    count_divisors_upto_z n d =
      count_divisors_upto_z n (d - 1).
Proof.
  intros n d Hd Hmod.
  unfold count_divisors_upto_z.
  replace (Z.to_nat d) with (S (Z.to_nat (d - 1))) by lia.
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) with d by lia.
  destruct (Z.eq_dec (Z.rem n d) 0) as [Hrem | Hrem].
  - exfalso.
    apply Hmod.
    exact Hrem.
  - rewrite Z.add_0_r.
    reflexivity.
Qed.

Lemma proof_of_count_divisors_entail_wit_1 : count_divisors_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_count_divisors_entail_wit_2_1 : count_divisors_entail_wit_2_1.
Proof.
  pre_process.
  entailer!; try lia.
  replace (d + 1 - 1) with d by lia.
  rewrite count_divisors_upto_z_step_divides by lia.
  lia.
Qed. 

Lemma proof_of_count_divisors_entail_wit_2_2 : count_divisors_entail_wit_2_2.
Proof.
  pre_process.
  entailer!; try lia.
  replace (d + 1 - 1) with d by lia.
  rewrite count_divisors_upto_z_step_not_divides by lia.
  lia.
Qed. 

Lemma proof_of_count_divisors_entail_wit_3 : count_divisors_entail_wit_3.
Proof.
  pre_process.
  entailer!; try lia.
  assert (Hd : d = n_pre + 1) by lia.
  subst d.
  replace (n_pre + 1 - 1) with n_pre in * by lia.
  rewrite count_divisors_spec_as_upto_z.
  assumption.
Qed. 
