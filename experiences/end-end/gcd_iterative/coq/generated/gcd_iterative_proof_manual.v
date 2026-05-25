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
From SimpleC.EE.CAV.verify_20260422_170350_gcd_iterative Require Import gcd_iterative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import gcd_iterative.
Local Open Scope sac.

Lemma gcd_iterative_step :
  forall a b g,
    b <> 0 ->
    gcd_iterative_spec a b g ->
    gcd_iterative_spec b (a % ( b )) g.
Proof.
  unfold gcd_iterative_spec.
  intros a b g Hb Hg.
  subst g.
  rewrite (Z.gcd_comm a b).
  rewrite <- (Z.gcd_rem a b Hb).
  apply Z.gcd_comm.
Qed.

Lemma gcd_iterative_zero_right :
  forall a g,
    0 <= a ->
    gcd_iterative_spec a 0 g ->
    g = a.
Proof.
  unfold gcd_iterative_spec.
  intros a g Ha Hg.
  subst g.
  apply Z.gcd_0_r_nonneg; lia.
Qed.

Lemma proof_of_gcd_iterative_entail_wit_1 : gcd_iterative_entail_wit_1.
Proof.
  pre_process.
  Exists (Z.gcd a_pre b_pre).
  entailer!;
    unfold gcd_iterative_spec;
    reflexivity.
Qed. 

Lemma proof_of_gcd_iterative_entail_wit_2 : gcd_iterative_entail_wit_2.
Proof.
  pre_process.
  Exists g_2.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - unfold gcd_iterative_spec in H4.
    subst g_2.
    unfold gcd_iterative_spec.
    rewrite (Z.gcd_comm a b).
    rewrite <- (Z.gcd_rem a b H).
    apply Z.gcd_comm.
  - assert (Hbpos: 0 < b) by lia.
    rewrite (Z.rem_mod_nonneg a b H0 Hbpos).
    pose proof (Z.mod_pos_bound a b Hbpos).
    lia.
  - assert (Hbpos: 0 < b) by lia.
    rewrite (Z.rem_mod_nonneg a b H0 Hbpos).
    pose proof (Z.mod_pos_bound a b Hbpos).
    lia.
Qed. 

Lemma proof_of_gcd_iterative_return_wit_1 : gcd_iterative_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (g = a) as Hgret.
  {
    subst b.
    eapply gcd_iterative_zero_right; [lia | exact H4].
  }
  subst g.
  assumption.
Qed. 
