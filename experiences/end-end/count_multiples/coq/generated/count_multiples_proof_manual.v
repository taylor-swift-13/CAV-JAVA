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
From SimpleC.EE.CAV.verify_20260422_152433_count_multiples Require Import count_multiples_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_multiples.
Require Import count_multiples_helper.
Local Open Scope sac.

Lemma count_multiples_upto_z_zero :
  forall k, count_multiples_upto_z k 0 = 0.
Proof.
  intros k.
  unfold count_multiples_upto_z.
  simpl.
  reflexivity.
Qed.

Lemma count_multiples_upto_z_step_multiple :
  forall k i,
    1 <= i ->
    Z.rem i k = 0 ->
    count_multiples_upto_z k i =
      count_multiples_upto_z k (i - 1) + 1.
Proof.
  intros k i Hi Hmod.
  unfold count_multiples_upto_z.
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1)))) with i by lia.
  destruct (Z.eq_dec (Z.rem i k) 0) as [Hrem | Hrem].
  - reflexivity.
  - exfalso.
    apply Hrem.
    exact Hmod.
Qed.

Lemma count_multiples_upto_z_step_not_multiple :
  forall k i,
    1 <= i ->
    Z.rem i k <> 0 ->
    count_multiples_upto_z k i =
      count_multiples_upto_z k (i - 1).
Proof.
  intros k i Hi Hmod.
  unfold count_multiples_upto_z.
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1)))) with i by lia.
  destruct (Z.eq_dec (Z.rem i k) 0) as [Hrem | Hrem].
  - exfalso.
    apply Hmod.
    exact Hrem.
  - rewrite Z.add_0_r.
    reflexivity.
Qed.

Lemma proof_of_count_multiples_entail_wit_1 : count_multiples_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_count_multiples_entail_wit_2_1 : count_multiples_entail_wit_2_1.
Proof.
  pre_process.
  entailer!; try lia.
  replace (i + 1 - 1) with i by lia.
  rewrite count_multiples_upto_z_step_multiple by lia.
  lia.
Qed. 

Lemma proof_of_count_multiples_entail_wit_2_2 : count_multiples_entail_wit_2_2.
Proof.
  pre_process.
  entailer!; try lia.
  replace (i + 1 - 1) with i by lia.
  rewrite count_multiples_upto_z_step_not_multiple by lia.
  lia.
Qed. 

Lemma proof_of_count_multiples_entail_wit_3 : count_multiples_entail_wit_3.
Proof.
  pre_process.
  entailer!; try lia.
  assert (Hi : i = n_pre + 1) by lia.
  subst i.
  replace (n_pre + 1 - 1) with n_pre in * by lia.
  rewrite count_multiples_spec_as_upto_z.
  assumption.
Qed. 
