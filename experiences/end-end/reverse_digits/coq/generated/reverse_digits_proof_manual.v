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
Require Import reverse_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import reverse_digits.
Require Import reverse_digits_verify_aux.
Local Open Scope sac.

Lemma reverse_digits_acc_fuel_nonpositive :
  forall fuel n acc, n <= 0 -> reverse_digits_acc_fuel n acc fuel = acc.
Proof.
  induction fuel; intros n acc Hn; simpl; auto.
  destruct (Z.leb n 0) eqn:Hleb; auto.
  apply Z.leb_gt in Hleb; lia.
Qed.

Lemma quot_10_lt_pos :
  forall n, 0 < n -> 0 <= n ÷ 10 < n.
Proof.
  intros n Hn.
  assert (Hq_nonneg : 0 <= n ÷ 10) by (apply Z.quot_pos; lia).
  assert (Hrem : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
  pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
  lia.
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

Lemma div_10_lt_pos :
  forall n, 0 < n -> 0 <= n / 10 < n.
Proof.
  intros n Hn.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt; lia.
Qed.

Lemma reverse_digits_acc_fuel_stable :
  forall (fuel : nat) (n acc : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    reverse_digits_acc_fuel n acc (fuel + extra)%nat =
    reverse_digits_acc_fuel n acc fuel.
Proof.
  intros fuel.
  induction fuel; intros n acc extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    pose proof (div_10_lt_pos n Hleb) as [Hq_nonneg Hq_lt].
    assert (Hq_fuel : (Z.to_nat (n / 10) <= fuel)%nat).
    {
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
    }
    rewrite (IHfuel (n / 10) (acc * 10 + n % 10) extra Hq_nonneg Hq_fuel).
    reflexivity.
Qed.

Lemma reverse_digits_acc_fuel_stable_ge :
  forall (n acc : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    reverse_digits_acc_fuel n acc fuel = reverse_digits_acc_z n acc.
Proof.
  intros n acc fuel Hn Hfuel.
  unfold reverse_digits_acc_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite reverse_digits_acc_fuel_stable; auto.
Qed.

Lemma reverse_digits_acc_z_step :
  forall n acc,
    0 < n ->
    reverse_digits_acc_z n acc =
    reverse_digits_acc_z (n ÷ 10) (acc * 10 + n % 10).
Proof.
  intros n acc Hn.
  unfold reverse_digits_acc_z at 1.
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
  pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
  replace (n / 10) with (n ÷ 10).
  apply reverse_digits_acc_fuel_stable_ge; auto.
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
  rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

Lemma reverse_digits_acc_z_zero :
  forall acc, reverse_digits_acc_z 0 acc = acc.
Proof.
  intros acc. unfold reverse_digits_acc_z. reflexivity.
Qed.

Lemma reverse_digits_acc_z_init :
  forall n,
    0 <= n ->
    reverse_digits_acc_z n 0 = reverse_digits_z n.
Proof.
  intros n Hn.
  unfold reverse_digits_acc_z, reverse_digits_z.
  reflexivity.
Qed.

Lemma reverse_digits_acc_fuel_acc_ge :
  forall fuel n acc,
    0 <= n ->
    0 <= acc ->
    acc <= reverse_digits_acc_fuel n acc fuel.
Proof.
  induction fuel; intros n acc Hn Hacc; simpl; auto.
  all: try lia.
  destruct (Z.leb n 0) eqn:Hleb.
  - lia.
  - apply Z.leb_gt in Hleb.
    set (acc' := acc * 10 + n % 10).
    assert (Hrem : 0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    assert (Hacc_le : acc <= acc') by (subst acc'; nia).
    pose proof (div_10_lt_pos n Hleb) as [Hq_nonneg Hq_lt].
    pose proof (IHfuel (n / 10) acc' Hq_nonneg ltac:(subst acc'; nia)).
    lia.
Qed.

Lemma reverse_digits_acc_z_acc_ge :
  forall n acc,
    0 <= n ->
    0 <= acc ->
    acc <= reverse_digits_acc_z n acc.
Proof.
  intros n acc Hn Hacc.
  unfold reverse_digits_acc_z.
  apply reverse_digits_acc_fuel_acc_ge; auto.
Qed.

Lemma proof_of_reverse_digits_safety_wit_3 : reverse_digits_safety_wit_3.
Proof.
  unfold reverse_digits_safety_wit_3.
  pre_process.
  entailer!.
  - assert (0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    change Int.min_signed with (-2147483648) in *.
    change Int.max_signed with 2147483647 in *.
    lia.
  - rewrite reverse_digits_acc_z_step in H5 by lia.
    pose proof (reverse_digits_acc_z_acc_ge (n ÷ 10) (ans * 10 + n % 10)).
    assert (0 <= n ÷ 10) by (apply Z.quot_pos; lia).
    assert (0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    specialize (H12 ltac:(lia) ltac:(nia)).
    lia.
Qed.

Lemma proof_of_reverse_digits_safety_wit_5 : reverse_digits_safety_wit_5.
Proof.
  unfold reverse_digits_safety_wit_5.
  pre_process.
  entailer!.
  - rewrite reverse_digits_acc_z_step in H5 by lia.
    pose proof (reverse_digits_acc_z_acc_ge (n ÷ 10) (ans * 10 + n % 10)).
    assert (0 <= n ÷ 10) by (apply Z.quot_pos; lia).
    assert (0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    specialize (H12 ltac:(lia) ltac:(nia)).
    lia.
Qed.

Lemma proof_of_reverse_digits_entail_wit_2 : reverse_digits_entail_wit_2.
Proof.
  unfold reverse_digits_entail_wit_2.
  pre_process.
Qed.

Lemma proof_of_reverse_digits_entail_wit_3 : reverse_digits_entail_wit_3.
Proof.
  unfold reverse_digits_entail_wit_3.
  pre_process.
  entailer!.
  - rewrite <- H5.
    symmetry. apply reverse_digits_acc_z_step; lia.
  - rewrite reverse_digits_acc_z_step in H5 by lia.
    pose proof (reverse_digits_acc_z_acc_ge (n ÷ 10) (ans * 10 + n % 10)).
    assert (0 <= n ÷ 10) by (apply Z.quot_pos; lia).
    assert (0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    specialize (H12 ltac:(lia) ltac:(nia)).
    lia.
  - assert (0 <= n % 10) by (apply Z.rem_bound_pos; lia).
    nia.
  - pose proof (quot_10_lt_pos n ltac:(lia)) as [_ Hq_lt]; lia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_reverse_digits_entail_wit_4 : reverse_digits_entail_wit_4.
Proof.
  unfold reverse_digits_entail_wit_4.
  pre_process.
  entailer!.
  - assert (n = 0) by lia.
    subst n.
    rewrite reverse_digits_acc_z_zero in H5.
    lia.
Qed.
