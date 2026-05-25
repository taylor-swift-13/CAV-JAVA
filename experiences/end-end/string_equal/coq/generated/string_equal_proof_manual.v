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
From SimpleC.EE.CAV.verify_20260423_021759_string_equal Require Import string_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma string_equal_nonzero_index_lt:
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    0 <= i ->
    i <= n ->
    Znth i (l ++ 0 :: nil) 0 <> 0 ->
    i < n.
Proof.
  intros l n i Hlen Hge Hle Hnz.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hnot].
  - exact Hlt.
  - assert (Hi : i = n) by lia.
    subst i.
    rewrite app_Znth2 in Hnz by lia.
    replace (n - Zlength l) with 0 in Hnz by lia.
    simpl in Hnz.
    contradiction Hnz; reflexivity.
Qed.

Lemma string_equal_zero_index_eq:
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    0 <= i ->
    i <= n ->
    (forall k : Z, 0 <= k < n -> Znth k l 0 <> 0) ->
    Znth i (l ++ 0 :: nil) 0 = 0 ->
    i = n.
Proof.
  intros l n i Hlen Hge Hle Hnz Hz.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hnot].
  - assert (Hval : Znth i l 0 <> 0) by (apply Hnz; lia).
    rewrite app_Znth1 in Hz by lia.
    contradiction Hval; exact Hz.
  - lia.
Qed.

Lemma proof_of_string_equal_entail_wit_2 : string_equal_entail_wit_2.
Proof.
  unfold string_equal_entail_wit_2.
  pre_process.
  assert (Hi_lt_na : i < na).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hi_lt_nb : i < nb).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hi_eq : Znth i la 0 = Znth i lb 0).
  {
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    exact H.
  }
  entailer!.
  intros k Hkrange.
  destruct (Z_lt_ge_dec k i) as [Hklt | Hkge].
  - apply H7; lia.
  - assert (k = i) by lia.
    subst k.
    exact Hi_eq.
Qed.

Lemma proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Proof.
  unfold string_equal_return_wit_1.
  pre_process.
  assert (Hi_lt_na : i < na).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hi_lt_nb : i < nb).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hneq : Znth i la 0 <> Znth i lb 0).
  {
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    exact H.
  }
  Left.
  Right.
  Exists i.
  entailer!.
Qed.

Lemma proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Proof.
  unfold string_equal_return_wit_2.
  pre_process.
  assert (Hi_eq_na : i = na).
  {
    eapply string_equal_zero_index_eq; eauto; lia.
  }
  assert (Hi_eq_nb : i = nb).
  {
    eapply string_equal_zero_index_eq; eauto; lia.
  }
  Right.
  entailer!.
  intros k Hkrange.
  apply H7.
  lia.
Qed.

Lemma proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Proof.
  unfold string_equal_return_wit_3.
  pre_process.
  assert (Hi_eq_na : i = na).
  {
    eapply string_equal_zero_index_eq; eauto; lia.
  }
  assert (Hi_lt_nb : i < nb).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hlen_neq : na <> nb) by lia.
  Left.
  Left.
  entailer!.
Qed.

Lemma proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
Proof.
  unfold string_equal_return_wit_4.
  pre_process.
  assert (Hi_lt_na : i < na).
  {
    eapply string_equal_nonzero_index_lt; eauto; lia.
  }
  assert (Hi_eq_nb : i = nb).
  {
    eapply string_equal_zero_index_eq; eauto; lia.
  }
  assert (Hlen_neq : na <> nb) by lia.
  Left.
  Left.
  entailer!.
Qed.
