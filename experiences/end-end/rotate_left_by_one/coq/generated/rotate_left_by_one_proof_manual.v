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
From SimpleC.EE.CAV.verify_20260422_215602_rotate_left_by_one Require Import rotate_left_by_one_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma rotate_left_by_one_step_list :
  forall (l l1 : list Z) (i n : Z),
    0 <= i ->
    i + 1 < n ->
    Zlength l = n ->
    Zlength l1 = i ->
    replace_Znth i
      (Znth (i + 1) (app l1 (sublist i n l)) 0)
      (app l1 (sublist i n l)) =
    app (l1 ++ (Znth (i + 1) l 0) :: nil) (sublist (i + 1) n l).
Proof.
  intros l l1 i n Hi Hlt Hlen Hl1.
  assert (Hread :
    Znth (i + 1) (app l1 (sublist i n l)) 0 = Znth (i + 1) l 0).
  {
    rewrite app_Znth2 by lia.
    rewrite Hl1.
    replace (i + 1 - i) with 1 by lia.
    rewrite (Znth_sublist i 1 n l 0) by lia.
    replace (1 + i) with (i + 1) by lia.
    reflexivity.
  }
  rewrite Hread.
  rewrite replace_Znth_app_r by lia.
  rewrite Hl1.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i n (i + 1) l) by (pose proof (Zlength_correct l); lia).
  rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
  simpl.
  rewrite replace_Znth_nothing by lia.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Lemma rotate_left_by_one_final_list :
  forall (l l1 : list Z) (n : Z),
    1 <= n ->
    Zlength l = n ->
    Zlength l1 = n - 1 ->
    replace_Znth (n - 1) (Znth 0 l 0)
      (app l1 (sublist (n - 1) n l)) =
    app l1 ((Znth 0 l 0) :: nil).
Proof.
  intros l l1 n Hn Hlen Hl1.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by (rewrite Hl1; lia).
  rewrite Hl1.
  replace (n - 1 - (n - 1)) with 0 by lia.
  replace (sublist (n - 1) n l) with (sublist (n - 1) ((n - 1) + 1) l)
    by (replace ((n - 1) + 1) with n by lia; reflexivity).
  rewrite (sublist_single (n - 1) l 0) by (pose proof (Zlength_correct l); lia).
  reflexivity.
Qed.

Lemma proof_of_rotate_left_by_one_entail_wit_1 : rotate_left_by_one_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  entailer!.
  replace n_pre with (Zlength l) by lia.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 

Lemma proof_of_rotate_left_by_one_entail_wit_2 : rotate_left_by_one_entail_wit_2.
Proof.
  pre_process.
  rewrite (rotate_left_by_one_step_list l l1_2 i n_pre) by lia.
  Exists (l1_2 ++ (Znth (i + 1) l 0) :: nil).
  entailer!.
  - intros k Hk.
    assert (Hcase : k < i \/ k = i) by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite H4; lia).
      apply H5.
      lia.
    + subst k.
      rewrite app_Znth2 by (rewrite H4; lia).
      rewrite H4.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in H4.
    rewrite Nat2Z.inj_add.
    lia.
Qed. 

Lemma proof_of_rotate_left_by_one_return_wit_1 : rotate_left_by_one_return_wit_1.
Proof.
  pre_process.
  assert (i_2 = n_pre - 1) by lia.
  subst i_2.
  rewrite H3.
  rewrite H8.
  rewrite (rotate_left_by_one_final_list l l1 n_pre) by lia.
  Exists (l1 ++ (Znth 0 l 0) :: nil).
  entailer!.
  - intros k Hk.
    split; intros Hcase.
    + rewrite app_Znth1 by (rewrite H8; lia).
      apply H5.
      rewrite H8.
      lia.
    + rewrite app_Znth2 by (rewrite H8; lia).
      rewrite H8.
      replace (k - (n_pre - 1)) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed. 
