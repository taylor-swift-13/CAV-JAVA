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
From SimpleC.SL Require Import Mem SeparationLogic StoreAux.
From SimpleC.EE.CAV.verify_20260422_164639_fibonacci_mod Require Import fibonacci_mod_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import fibonacci_mod.
Local Open Scope sac.

Lemma fib_mod_z_0 : forall m, fib_mod_z 0 m = 0.
Proof.
  intros m.
  reflexivity.
Qed.

Lemma fib_mod_z_1 : forall m, fib_mod_z 1 m = Z.rem 1 m.
Proof.
  intros m.
  reflexivity.
Qed.

Lemma fib_mod_nat_succ :
  forall n m, fib_mod_nat (S n) m = snd (fib_mod_pair n m).
Proof.
  intros n m.
  reflexivity.
Qed.

Lemma fib_mod_nat_step :
  forall n m,
    fib_mod_nat (S (S n)) m =
    Z.rem (fib_mod_nat n m + fib_mod_nat (S n) m) m.
Proof.
  intros n m.
  rewrite fib_mod_nat_succ.
  unfold fib_mod_nat.
  simpl.
  reflexivity.
Qed.

Lemma fib_mod_z_step :
  forall i m,
    2 <= i ->
    fib_mod_z i m =
    Z.rem (fib_mod_z (i - 2) m + fib_mod_z (i - 1) m) m.
Proof.
  intros i m Hi.
  unfold fib_mod_z.
  replace (Z.to_nat i) with (S (S (Z.to_nat (i - 2)))).
  - rewrite fib_mod_nat_step.
    replace (Z.to_nat (i - 1)) with (S (Z.to_nat (i - 2))) by lia.
    reflexivity.
  - apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma Z_rem_nonneg_bound :
  forall x m,
    0 <= x ->
    0 < m ->
    0 <= Z.rem x m < m.
Proof.
  intros x m Hx Hm.
  apply Z.rem_bound_pos; lia.
Qed.

Lemma proof_of_fibonacci_mod_entail_wit_1 : fibonacci_mod_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - pose proof (Z_rem_nonneg_bound 1 mod_pre ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (Z_rem_nonneg_bound 1 mod_pre ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_fibonacci_mod_entail_wit_2 : fibonacci_mod_entail_wit_2.
Proof.
  pre_process.
  entailer!; subst a; subst b.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - pose proof (Z_rem_nonneg_bound
      (fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre)
      mod_pre ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (Z_rem_nonneg_bound
      (fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre)
      mod_pre ltac:(lia) ltac:(lia)).
    lia.
  - replace ((i + 1) - 1) with i by lia.
    rewrite (fib_mod_z_step i mod_pre) by lia.
    reflexivity.
  - replace ((i + 1) - 2) with (i - 1) by lia.
    reflexivity.
Qed.

Lemma proof_of_fibonacci_mod_return_wit_1 : fibonacci_mod_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  rewrite fib_mod_z_0.
  reflexivity.
Qed.
