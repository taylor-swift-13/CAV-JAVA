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
Require Import string_reverse_copy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma Zlength_rev_Z : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  rewrite length_rev.
  reflexivity.
Qed.

Lemma string_reverse_copy_replace_Znth :
  forall (n i : Z) (l d : list Z),
    0 <= i ->
    i < n ->
    Zlength l = n ->
    Zlength d = n + 1 ->
    replace_Znth i (Znth (n - 1 - i) (l ++ 0 :: nil) 0)
      (app (rev (sublist (n - i) n l)) (sublist i (n + 1) d)) =
    app (rev (sublist (n - (i + 1)) n l)) (sublist (i + 1) (n + 1) d).
Proof.
  intros n i l d Hi_nonneg Hi_lt Hl Hd.
  assert (Hsrc :
    Znth (n - 1 - i) (l ++ 0 :: nil) 0 = Znth (n - 1 - i) l 0).
  {
    rewrite app_Znth1 by lia.
    reflexivity.
  }
  rewrite Hsrc.
  assert (Hpref_len : Zlength (rev (sublist (n - i) n l)) = i).
  {
    rewrite Zlength_rev_Z.
    rewrite Zlength_sublist by lia.
    lia.
  }
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  rewrite Hpref_len.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i (n + 1) (i + 1) d) by (pose proof (Zlength_correct d); lia).
  rewrite (sublist_single i d 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  replace (n - (i + 1)) with (n - 1 - i) by lia.
  rewrite (sublist_split (n - 1 - i) n (n - i) l) by (pose proof (Zlength_correct l); lia).
  replace (sublist (n - 1 - i) (n - i) l) with (cons (Znth (n - 1 - i) l 0) nil).
  2: {
    rewrite <- (sublist_single (n - 1 - i) l 0) by (rewrite <- Zlength_correct; lia).
    replace (n - 1 - i + 1) with (n - i) by lia.
    reflexivity.
  }
  rewrite rev_app_distr.
  simpl.
  unfold replace_Znth.
  simpl.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Lemma string_reverse_copy_final_replace :
  forall (n : Z) (l d : list Z),
    0 <= n ->
    Zlength l = n ->
    Zlength d = n + 1 ->
    replace_Znth n 0
      (app (rev (sublist (n - n) n l)) (sublist n (n + 1) d)) =
    app (rev l) (cons 0 nil).
Proof.
  intros n l d Hn Hl Hd.
  replace (n - n) with 0 by lia.
  rewrite sublist_self by lia.
  assert (Hpref_len : Zlength (rev l) = n).
  {
    rewrite Zlength_rev_Z.
    lia.
  }
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  rewrite Hpref_len.
  replace (n - n) with 0 by lia.
  rewrite (sublist_split n (n + 1) (n + 1) d) by (pose proof (Zlength_correct d); lia).
  rewrite (sublist_nil d (n + 1) (n + 1)) by lia.
  rewrite app_nil_r.
  rewrite (sublist_single n d 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  reflexivity.
Qed.

Lemma proof_of_string_reverse_copy_entail_wit_1 : string_reverse_copy_entail_wit_1.
Proof.
  pre_process.
  replace (app (rev (sublist (n_pre - 0) n_pre l)) (sublist 0 (n_pre + 1) d)) with d.
  - entailer!.
  - rewrite sublist_nil by lia.
    simpl.
    rewrite sublist_self by lia.
    reflexivity.
Qed.

Lemma proof_of_string_reverse_copy_entail_wit_2 : string_reverse_copy_entail_wit_2.
Proof.
  pre_process.
  rewrite string_reverse_copy_replace_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_string_reverse_copy_return_wit_1 : string_reverse_copy_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  rewrite string_reverse_copy_final_replace by lia.
  entailer!.
Qed.
