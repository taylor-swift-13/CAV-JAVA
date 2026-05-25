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
From SimpleC.EE.CAV.verify_20260423_121024_count_digits Require Import count_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_digits.
Local Open Scope sac.

Lemma pow10_pos : forall c, 0 <= c -> 0 < 10 ^ c.
Proof.
  intros c Hc.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma pow10_succ_mul : forall c, 0 <= c -> 10 ^ (c + 1) = 10 ^ c * 10.
Proof.
  intros c Hc.
  replace (c + 1) with (Z.succ c) by lia.
  rewrite Z.pow_succ_r by lia.
  lia.
Qed.

Lemma div10_bounds_pos :
  forall n,
    0 < n ->
    0 <= n ÷ 10 /\
    n ÷ 10 <= n - 1 /\
    10 * (n ÷ 10) <= n /\
    n < 10 * (n ÷ 10 + 1).
Proof.
  intros n Hn.
  assert (Hdiv_nonneg : 0 <= n ÷ 10).
  {
    apply Z.quot_pos; lia.
  }
  assert (Hmod := Z.rem_bound_pos n 10 ltac:(lia) ltac:(lia)).
  assert (Hdivmod := Z.quot_rem n 10 ltac:(lia)).
  rewrite Z.mul_comm in Hdivmod.
  destruct Hmod as [Hmod_low Hmod_high].
  split.
  - lia.
  - split.
    + lia.
    + split; lia.
Qed.

Lemma proof_of_count_digits_entail_wit_2 : count_digits_entail_wit_2.
Proof.
  unfold count_digits_entail_wit_2.
  pre_process.
Qed.

Lemma proof_of_count_digits_entail_wit_3 : count_digits_entail_wit_3.
Proof.
  unfold count_digits_entail_wit_3.
  pre_process.
  entailer!.
  - assert (Hn_pos : 0 < n) by lia.
    pose proof (div10_bounds_pos n Hn_pos) as (Hq_nonneg & Hq_le & Hq_low & Hq_high).
    rewrite pow10_succ_mul by lia.
    assert (Hpow_pos : 0 < 10 ^ cnt) by (apply pow10_pos; lia).
    nia.
  - assert (Hn_pos : 0 < n) by lia.
    pose proof (div10_bounds_pos n Hn_pos) as (Hq_nonneg & Hq_le & Hq_low & Hq_high).
    rewrite pow10_succ_mul by lia.
    assert (Hpow_nonneg : 0 <= 10 ^ cnt) by (apply Z.pow_nonneg; lia).
    nia.
  - intros _.
    replace (cnt + 1 - 1) with cnt by lia.
    assert (Hpow_nonneg : 0 <= 10 ^ cnt) by (apply Z.pow_nonneg; lia).
    assert (1 <= n) by lia.
    nia.
  - assert (Hn_pos : 0 < n) by lia.
    pose proof (div10_bounds_pos n Hn_pos) as (Hq_nonneg & Hq_le & Hq_low & Hq_high).
    lia.
  - assert (Hn_pos : 0 < n) by lia.
    pose proof (div10_bounds_pos n Hn_pos) as (Hq_nonneg & Hq_le & Hq_low & Hq_high).
    lia.
Qed.

Lemma proof_of_count_digits_return_wit_1 : count_digits_return_wit_1.
Proof.
  unfold count_digits_return_wit_1.
  pre_process.
  entailer!.
  unfold count_digits_spec.
  left.
  lia.
Qed.

Lemma proof_of_count_digits_return_wit_2 : count_digits_return_wit_2.
Proof.
  unfold count_digits_return_wit_2.
  pre_process.
  entailer!.
  unfold count_digits_spec.
  right.
  assert (n = 0) by lia.
  subst n.
  assert (cnt > 0).
  {
    destruct (Z_lt_le_dec 0 cnt) as [Hcnt_pos | Hcnt_nonpos].
    - lia.
    - assert (cnt = 0) by lia.
      specialize (H5 H14).
      lia.
  }
  split.
  - lia.
  - split.
    + lia.
    + split.
      * apply H6; lia.
      * replace (0 + 1) with 1 in H8 by lia.
        rewrite Z.mul_1_r in H8.
        exact H8.
Qed.
