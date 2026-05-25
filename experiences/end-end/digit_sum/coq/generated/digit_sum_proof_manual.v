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
From SimpleC.EE.CAV.verify_20260422_154652_digit_sum Require Import digit_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import digit_sum.
Local Open Scope sac.

Lemma digit_sum_fuel_nonpositive :
  forall fuel n, n <= 0 -> digit_sum_fuel n fuel = 0.
Proof.
  induction fuel; intros n Hn; simpl; auto.
  destruct (Z.leb n 0) eqn:Hleb; auto.
  apply Z.leb_gt in Hleb; lia.
Qed.

Lemma div_10_lt_pos :
  forall n, 0 < n -> 0 <= n / 10 < n.
Proof.
  intros n Hn.
  assert (Hdiv_nonneg : 0 <= n / 10) by (apply Z.div_pos; lia).
  assert (Hdiv_lt : n / 10 < n).
  {
    apply Z.div_lt_upper_bound; lia.
  }
  lia.
Qed.

Lemma quot_10_lt_pos :
  forall n, 0 < n -> 0 <= n ÷ 10 < n.
Proof.
  intros n Hn.
  replace (n ÷ 10) with (n / 10).
  - apply div_10_lt_pos; lia.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_10_bounds_pos :
  forall n, 0 < n -> 0 <= n % 10 <= n.
Proof.
  intros n Hn.
  assert (Hrem : 0 <= n % 10 < 10) by (apply Z.rem_bound_pos; lia).
  pose proof (Z.quot_pos n 10 ltac:(lia) ltac:(lia)) as Hq_nonneg.
  pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
  lia.
Qed.

Lemma digit_sum_fuel_stable :
  forall (fuel : nat) (n : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_sum_fuel n (fuel + extra)%nat = digit_sum_fuel n fuel.
Proof.
  intros fuel.
  induction fuel; intros n extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    f_equal.
    rewrite (IHfuel (n / 10) extra).
    + reflexivity.
    + pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
      lia.
    + pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma digit_sum_fuel_stable_ge :
  forall (n : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_sum_fuel n fuel = digit_sum_z n.
Proof.
  intros n fuel Hn Hfuel.
  unfold digit_sum_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite digit_sum_fuel_stable; auto.
Qed.

Lemma digit_sum_z_step :
  forall n,
    0 < n ->
    digit_sum_z n = Z.rem n 10 + digit_sum_z (n ÷ 10).
Proof.
  intros n Hn.
  unfold digit_sum_z at 1.
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk. simpl.
  destruct (Z.leb n 0) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  f_equal.
  replace (n / 10) with (n ÷ 10).
  - apply digit_sum_fuel_stable_ge.
    + pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
      lia.
    + pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
      assert (HkZ : Z.of_nat k = n - 1).
      {
        apply (f_equal Z.of_nat) in Hk.
        rewrite Nat2Z.inj_succ in Hk.
        rewrite Z2Nat.id in Hk by lia.
        lia.
      }
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      lia.
  - apply Z.quot_div_nonneg; lia.
Qed.

Lemma proof_of_digit_sum_safety_wit_3 : digit_sum_safety_wit_3.
Proof.
  unfold digit_sum_safety_wit_3.
  pre_process.
  entailer!.
  - pose proof (rem_10_bounds_pos n ltac:(lia)) as [Hrem_nonneg Hrem_le].
    lia.
  - pose proof (rem_10_bounds_pos n ltac:(lia)) as [Hrem_nonneg Hrem_le].
    lia.
Qed.

Lemma proof_of_digit_sum_entail_wit_3 : digit_sum_entail_wit_3.
Proof.
  unfold digit_sum_entail_wit_3.
  pre_process.
  entailer!.
  - rewrite <- H4.
    rewrite (digit_sum_z_step n ltac:(lia)).
    lia.
  - pose proof (quot_10_lt_pos n ltac:(lia)) as [Hq_nonneg Hq_lt].
    pose proof (rem_10_bounds_pos n ltac:(lia)) as [Hrem_nonneg Hrem_le].
    pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
    lia.
  - pose proof (rem_10_bounds_pos n ltac:(lia)) as [Hrem_nonneg Hrem_le].
    lia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_digit_sum_return_wit_1 : digit_sum_return_wit_1.
Proof.
  unfold digit_sum_return_wit_1.
  pre_process.
  entailer!.
  assert (n = 0) by lia.
  subst n.
  replace (digit_sum_z 0) with 0 in H4 by (unfold digit_sum_z; reflexivity).
  lia.
Qed.
