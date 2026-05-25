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
From SimpleC.EE.CAV.verify_20260422_182720_lcm_simple Require Import lcm_simple_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import lcm_simple.
Local Open Scope sac.

Lemma lcm_simple_value_pos :
  forall a b,
    1 <= a ->
    1 <= b ->
    0 < lcm_simple_value a b.
Proof.
  intros a b Ha Hb.
  unfold lcm_simple_value.
  pose proof (Z.lcm_nonneg a b) as Hnonneg.
  destruct (Z.eq_dec (Z.lcm a b) 0) as [Hzero | Hnonzero].
  - apply Z.lcm_eq_0 in Hzero.
    lia.
  - 
  lia.
Qed.

Lemma lcm_simple_value_ge_left :
  forall a b,
    1 <= a ->
    1 <= b ->
    a <= lcm_simple_value a b.
Proof.
  intros a b Ha Hb.
  unfold lcm_simple_value.
  apply Z.divide_pos_le.
  - pose proof (lcm_simple_value_pos a b Ha Hb).
    unfold lcm_simple_value in H.
    exact H.
  - apply Z.divide_lcm_l.
Qed.

Lemma lcm_simple_next_le_lcm :
  forall a b x k,
    Z.rem x b <> 0 ->
    1 <= a ->
    1 <= b ->
    x = a * k ->
    x <= lcm_simple_value a b ->
    1 <= k ->
    x + a <= lcm_simple_value a b.
Proof.
  intros a b x k Hmod Ha Hb Hx Hle Hk.
  unfold lcm_simple_value in *.
  pose proof (Z.divide_lcm_l a b) as Hdiva.
  destruct Hdiva as [m HL].
  assert (k < m) as Hkm.
  {
    assert (k <= m) by nia.
    destruct (Z.eq_dec k m) as [Heq | Hneq].
    - exfalso.
      subst m.
      assert (HxL : x = Z.lcm a b) by nia.
      apply Hmod.
      rewrite HxL.
      apply Z.rem_divide; try lia.
      apply Z.divide_lcm_r.
    - lia.
  }
  nia.
Qed.

Lemma lcm_simple_exit_eq :
  forall a b x k,
    Z.rem x b = 0 ->
    1 <= a ->
    1 <= b ->
    1 <= k ->
    x = a * k ->
    x <= lcm_simple_value a b ->
    x = lcm_simple_value a b.
Proof.
  intros a b x k Hmod Ha Hb Hk Hx Hle.
  unfold lcm_simple_value in *.
  assert (Ha_div : (a | x)).
  { exists k. nia. }
  assert (Hb_div : (b | x)).
  { apply Z.rem_divide; lia. }
  pose proof (Z.lcm_least a b x Ha_div Hb_div) as HLdivx.
  assert (0 < x) by nia.
  pose proof (Z.divide_pos_le (Z.lcm a b) x H HLdivx) as Hlower.
  lia.
Qed.

Lemma proof_of_lcm_simple_safety_wit_3 : lcm_simple_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - assert (Hnext : x + a_pre <= lcm_simple_value a_pre b_pre).
    {
      apply (lcm_simple_next_le_lcm a_pre b_pre x k).
      - exact H.
      - lia.
      - lia.
      - exact H4.
      - exact H5.
      - lia.
    }
    lia.
Qed. 

Lemma proof_of_lcm_simple_entail_wit_1 : lcm_simple_entail_wit_1.
Proof.
  pre_process.
  Exists 1.
  entailer!.
  apply lcm_simple_value_ge_left; lia.
Qed. 

Lemma proof_of_lcm_simple_entail_wit_2 : lcm_simple_entail_wit_2.
Proof.
  pre_process.
  Exists (k_2 + 1).
  entailer!.
  apply (lcm_simple_next_le_lcm a_pre b_pre x k_2); try lia; auto.
Qed. 

Lemma proof_of_lcm_simple_return_wit_1 : lcm_simple_return_wit_1.
Proof.
  pre_process.
  unfold lcm_simple_spec.
  entailer!.
  apply lcm_simple_exit_eq with (k := k); auto.
Qed. 
