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
From SimpleC.EE.CAV.verify_20260422_091409_binary_search Require Import binary_search_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma binary_search_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
Proof.
  intros x Hx.
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  - subst. change (0 ÷ 2) with 0. lia.
  - split.
    + apply Z.quot_pos; lia.
    + assert (x ÷ 2 < x) by (apply Z.quot_lt; lia).
      lia.
Qed.

Lemma proof_of_binary_search_safety_wit_4 : binary_search_safety_wit_4.
Proof.
  pre_process.
  prop_apply (store_int_range (&("left")) left).
  Intros.
  prop_apply (store_int_range (&("right")) right).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_quot2_bounds; lia).
  entailer!.
Qed.

Lemma proof_of_binary_search_entail_wit_1 : binary_search_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_binary_search_entail_wit_2 : binary_search_entail_wit_2.
Proof.
  pre_process.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_quot2_bounds; lia).
  entailer!.
Qed.

Lemma proof_of_binary_search_entail_wit_3_1 : binary_search_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hupper_new:
    forall j, mid <= j < n_pre -> target_pre < Znth j l 0).
  {
    intros j Hj.
    destruct (Z.eq_dec j mid) as [Heq | Hneq].
    - subst. lia.
    - assert (mid < j) by lia.
      assert (Hmono: Znth mid l 0 <= Znth j l 0).
      {
        match goal with
        | Hsorted: forall i k, _ -> Znth i l 0 <= Znth k l 0 |- _ =>
            apply (Hsorted mid j); lia
        end.
      }
      lia.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
  intros i Hi.
  apply Hupper_new; lia.
Qed.

Lemma proof_of_binary_search_entail_wit_3_2 : binary_search_entail_wit_3_2.
Proof.
  pre_process.
  assert (Hlower_new:
    forall j, 0 <= j < mid + 1 -> Znth j l 0 < target_pre).
  {
    intros j Hj.
    destruct (Z_lt_dec j left) as [Hjleft | Hnotleft].
    - match goal with
      | Hlower: forall q, 0 <= q /\ q < left -> Znth q l 0 < target_pre |- _ =>
          apply Hlower; lia
      end.
    - assert (j <= mid) by lia.
      assert (Hmono: Znth j l 0 <= Znth mid l 0).
      {
        match goal with
        | Hsorted: forall i k, _ -> Znth i l 0 <= Znth k l 0 |- _ =>
            apply (Hsorted j mid); lia
        end.
      }
      lia.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed.
