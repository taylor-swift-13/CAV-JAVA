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
From SimpleC.EE.CAV.verify_20260423_050130_sum_to_n Require Import sum_to_n_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma sum_to_n_consecutive_product_even : forall i, Z.Even ((i - 1) * i).
Proof.
  intro i.
  destruct (Z.Even_or_Odd i) as [[k Hk] | [k Hk]]; subst i.
  - exists ((2 * k - 1) * k). nia.
  - exists (k * (2 * k + 1)). nia.
Qed.

Lemma sum_to_n_half_consecutive_exact :
  forall i, 2 * (((i - 1) * i) ÷ 2) = (i - 1) * i.
Proof.
  intro i.
  destruct (sum_to_n_consecutive_product_even i) as [k Hk].
  rewrite Hk.
  replace (2 * k) with (k * 2) by lia.
  rewrite Z.quot_mul by lia.
  lia.
Qed.

Lemma sum_to_n_triangular_step :
  forall i, 1 <= i ->
    ((i - 1) * i) ÷ 2 + i = (i * (i + 1)) ÷ 2.
Proof.
  intros i Hi.
  apply Z.quot_unique_exact.
  - lia.
  - pose proof (sum_to_n_half_consecutive_exact i) as Hhalf.
    nia.
Qed.

Lemma sum_to_n_triangular_mono :
  forall i n, 0 <= i -> i <= n ->
    (i * (i + 1)) ÷ 2 <= (n * (n + 1)) ÷ 2.
Proof.
  intros i n Hi Hin.
  apply Z.quot_le_mono.
  - lia.
  - nia.
Qed.

Lemma sum_to_n_succ_bound_from_tri :
  forall n, 1 <= n ->
    n * (n + 1) ÷ 2 <= INT_MAX ->
    n + 1 <= INT_MAX.
Proof.
  intros n Hn Htri.
  destruct (Z.eq_dec n 1) as [-> | Hne].
  - lia.
  - assert (2 <= n) by lia.
    assert (n + 1 <= n * (n + 1) ÷ 2).
    { apply Z.quot_le_lower_bound; nia. }
    lia.
Qed.

Lemma proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - rewrite sum_to_n_triangular_step by lia.
    assert (0 <= (i * (i + 1)) ÷ 2) by (apply Z.quot_pos; nia).
    lia.
  - rewrite sum_to_n_triangular_step by lia.
    assert (Hnonneg_i : 0 <= i) by lia.
    assert (Hle_in : i <= n_pre) by lia.
    pose proof (sum_to_n_triangular_mono i n_pre Hnonneg_i Hle_in).
    lia.
Qed.

Lemma proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - assert (n_pre + 1 <= INT_MAX).
    { apply sum_to_n_succ_bound_from_tri; lia. }
    lia.
Qed.

Lemma proof_of_sum_to_n_entail_wit_1 : sum_to_n_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_sum_to_n_entail_wit_3 : sum_to_n_entail_wit_3.
Proof.
  pre_process.
  rewrite sum_to_n_triangular_step by lia.
  entailer!.
Qed.

Lemma proof_of_sum_to_n_entail_wit_4 : sum_to_n_entail_wit_4.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.

Lemma proof_of_sum_to_n_entail_wit_5 : sum_to_n_entail_wit_5.
Proof.
  pre_process.
  assert (i = n_pre + 1) by lia.
  subst i.
  replace (n_pre + 1 - 1) with n_pre in H2 by lia.
  subst ret.
  entailer!.
  replace (n_pre + 1 - 1) with n_pre by lia.
  reflexivity.
Qed.
