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
From SimpleC.EE.CAV.verify_20260422_212943_reverse_copy Require Import reverse_copy_goal.
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

Lemma reverse_copy_replace_Znth :
  forall (n i : Z) (ls ld : list Z),
    0 <= i ->
    i < n ->
    Zlength ls = n ->
    Zlength ld = n ->
    replace_Znth i (Znth (n - 1 - i) ls 0)
      (app (rev (sublist (n - i) n ls)) (sublist i n ld)) =
    app (rev (sublist (n - (i + 1)) n ls)) (sublist (i + 1) n ld).
Proof.
  intros n i ls ld Hi_nonneg Hi_lt Hls Hld.
  assert (Hpref_len : Zlength (rev (sublist (n - i) n ls)) = i).
  {
    rewrite Zlength_rev_Z.
    rewrite Zlength_sublist by lia.
    lia.
  }
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  rewrite Hpref_len.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i n (i + 1) ld) by (pose proof (Zlength_correct ld); lia).
  rewrite (sublist_single i ld 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  replace (n - (i + 1)) with (n - 1 - i) by lia.
  rewrite (sublist_split (n - 1 - i) n (n - i) ls) by (pose proof (Zlength_correct ls); lia).
  replace (sublist (n - 1 - i) (n - i) ls) with (cons (Znth (n - 1 - i) ls 0) nil).
  2: {
    rewrite <- (sublist_single (n - 1 - i) ls 0) by (rewrite <- Zlength_correct; lia).
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

Lemma proof_of_reverse_copy_entail_wit_1 : reverse_copy_entail_wit_1.
Proof.
  pre_process.
  replace (app (rev (sublist (n_pre - 0) n_pre ls)) (sublist 0 n_pre ld)) with ld.
  - entailer!.
  - rewrite sublist_nil by lia.
    simpl.
    rewrite sublist_self by lia.
    reflexivity.
Qed.

Lemma proof_of_reverse_copy_entail_wit_2 : reverse_copy_entail_wit_2.
Proof.
  pre_process.
  rewrite reverse_copy_replace_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_reverse_copy_return_wit_1 : reverse_copy_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  replace (app (rev (sublist (n_pre - n_pre) n_pre ls)) (sublist n_pre n_pre ld)) with (rev ls).
  - entailer!.
  - replace (n_pre - n_pre) with 0 by lia.
    rewrite sublist_self by lia.
    rewrite sublist_nil by lia.
    rewrite app_nil_r.
    reflexivity.
Qed.
