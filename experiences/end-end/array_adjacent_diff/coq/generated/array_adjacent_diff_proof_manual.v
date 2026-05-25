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
From SimpleC.EE.CAV.verify_20260422_015904_array_adjacent_diff Require Import array_adjacent_diff_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma adjacent_diff_step_list :
  forall (la lo l1 : list Z) (i n : Z),
    0 <= i ->
    i + 1 < n ->
    Zlength la = n ->
    Zlength lo = n - 1 ->
    Zlength l1 = i ->
    replace_Znth i (Znth (i + 1) la 0 - Znth i la 0)
      (app l1 (sublist i (n - 1) lo)) =
    app (l1 ++ (Znth (i + 1) la 0 - Znth i la 0) :: nil)
        (sublist (i + 1) (n - 1) lo).
Proof.
  intros la lo l1 i n Hi Hlt Hla Hlo Hl1.
  rewrite replace_Znth_app_r by lia.
  rewrite Hl1.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i (n - 1) (i + 1) lo) by (rewrite Zlength_correct in Hlo; lia).
  rewrite (sublist_single i lo 0) by (rewrite Zlength_correct in Hlo; lia).
  simpl.
  rewrite replace_Znth_nothing by lia.
  simpl.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_array_adjacent_diff_safety_wit_4 : array_adjacent_diff_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - match goal with
    | Hdiff : forall j : Z, (0 <= j /\ j < n_pre - 1) -> _ |- _ =>
        assert (Hrange : 0 <= i /\ i < n_pre - 1) by lia;
        pose proof (Hdiff i Hrange) as Hbound;
        lia
    end.
  - match goal with
    | Hdiff : forall j : Z, (0 <= j /\ j < n_pre - 1) -> _ |- _ =>
        assert (Hrange : 0 <= i /\ i < n_pre - 1) by lia;
        pose proof (Hdiff i Hrange) as Hbound;
        lia
    end.
Qed.

Lemma proof_of_array_adjacent_diff_entail_wit_1 : array_adjacent_diff_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  entailer!.
  replace (n_pre - 1) with (Zlength lo) by lia.
  rewrite sublist_self by reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_array_adjacent_diff_entail_wit_2 : array_adjacent_diff_entail_wit_2.
Proof.
  pre_process.
  rewrite (adjacent_diff_step_list la lo l1_2 i_2 n_pre) by lia.
  Exists (l1_2 ++ (Znth (i_2 + 1) la 0 - Znth i_2 la 0) :: nil).
  entailer!.
  - intros k Hk.
    assert (Hcase : k < i_2 \/ k = i_2) by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite H4; lia).
      apply H5.
      lia.
    + subst k.
      rewrite app_Znth2 by (rewrite H4; lia).
      rewrite H4.
      replace (i_2 - i_2) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in H4.
    rewrite Nat2Z.inj_add.
    lia.
Qed.

Lemma proof_of_array_adjacent_diff_return_wit_1 : array_adjacent_diff_return_wit_1.
Proof.
  pre_process.
  assert (i_3 = n_pre - 1) by lia.
  subst i_3.
  rewrite sublist_nil by lia.
  rewrite app_nil_r.
  Exists l1.
  entailer!.
  intros k Hk.
  apply H5.
  rewrite H10.
  lia.
Qed.
