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
From SimpleC.EE.CAV.verify_20260422_180530_is_prime_simple Require Import is_prime_simple_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import is_prime_simple.
Local Open Scope sac.

Lemma proof_of_is_prime_simple_return_wit_1 : is_prime_simple_return_wit_1.
Proof.
  unfold is_prime_simple_return_wit_1.
  pre_process.
  entailer!.
  unfold is_prime_simple_spec, is_prime_z.
  right.
  split.
  - reflexivity.
  - intros [Hprime _].
    lia.
Qed.

Lemma proof_of_is_prime_simple_return_wit_2 : is_prime_simple_return_wit_2.
Proof.
  unfold is_prime_simple_return_wit_2.
  pre_process.
  entailer!.
  unfold is_prime_simple_spec, is_prime_z.
  right.
  split.
  - reflexivity.
  - intros [_ Hprime].
    assert (Hd_range : 2 <= d < n_pre) by lia.
    specialize (Hprime d Hd_range).
    contradiction.
Qed.

Lemma proof_of_is_prime_simple_return_wit_3 : is_prime_simple_return_wit_3.
Proof.
  unfold is_prime_simple_return_wit_3.
  pre_process.
  entailer!.
  unfold is_prime_simple_spec, is_prime_z.
  left.
  split.
  - reflexivity.
  - split.
    + lia.
    + intros k Hrange.
      apply H1.
      lia.
Qed.
