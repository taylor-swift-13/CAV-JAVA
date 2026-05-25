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
From SimpleC.EE.CAV.verify_20260422_081724_array_second_largest Require Import array_second_largest_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_second_largest_entail_wit_1_1 : array_second_largest_entail_wit_1_1.
Proof.
  pre_process.
  Exists 0 1.
  entailer!.
  intros k Hk.
  destruct Hk as [[Hk0 Hk2] Hk_ne_top].
  assert (Hcase : k = 0 \/ k = 1) by lia.
  destruct Hcase as [Hk_eq | Hk_eq]; subst; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_1_2 : array_second_largest_entail_wit_1_2.
Proof.
  pre_process.
  Exists 1 0.
  entailer!.
  - intros k Hk.
    destruct Hk as [[Hk0 Hk2] Hk_ne_top].
    assert (Hcase : k = 0 \/ k = 1) by lia.
    destruct Hcase as [Hk_eq | Hk_eq]; subst; try lia.
  - specialize (H3 0 1).
    lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_1 : array_second_largest_entail_wit_2_1.
Proof.
  pre_process.
  Exists top_2 i.
  entailer!.
  intros k Hk.
  destruct Hk as [[Hk0 Hklt] Hk_ne_top].
  assert (Hcase : k < i \/ k = i) by lia.
  destruct Hcase as [Hk_old | Hk_new].
  - destruct (Z.eq_dec k top_2).
    + subst. lia.
    + match goal with
      | Hforall: forall k : Z, 0 <= k < i /\ k <> top_2 -> Znth k l 0 <= max2 |- _ =>
          specialize (Hforall k); lia
      end.
  - subst. lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_2 : array_second_largest_entail_wit_2_2.
Proof.
  pre_process.
  Exists i top_2.
  entailer!.
  - intros k Hk.
    destruct Hk as [[Hk0 Hklt] Hk_ne_top].
    assert (Hcase : k < i \/ k = i) by lia.
    destruct Hcase as [Hk_old | Hk_new].
    + match goal with
      | Hforall: forall k : Z, 0 <= k < i /\ k <> top_2 -> Znth k l 0 <= max2 |- _ =>
          specialize (Hforall k); lia
      end.
    + subst. lia.
  - match goal with
    | Hdist: forall p q : Z, 0 <= p < q /\ q < n_pre -> Znth p l 0 <> Znth q l 0,
      Htop: Znth top_2 l 0 = max1 |- _ =>
        pose proof (Hdist top_2 i ltac:(lia)) as Hneq;
        rewrite Htop in Hneq;
        lia
    end.
Qed.
