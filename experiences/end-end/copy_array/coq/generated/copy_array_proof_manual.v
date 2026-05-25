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
From SimpleC.EE.CAV.verify_20260422_133747_copy_array Require Import copy_array_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Proof.
  pre_process.
  Exists ld.
  Exists nil.
  entailer!.
Qed.

Lemma proof_of_copy_array_entail_wit_2 : copy_array_entail_wit_2.
Proof.
  pre_process.
  Exists (sublist (i + 1) n_pre ld).
  Exists l1'.
  entailer!.
  - intros k Hk.
    rewrite Znth_sublist by lia.
    replace (k + (i + 1)) with (i + 1 + k) by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  replace (app l1 l2) with ls.
  - entailer!.
  - apply (proj2 (list_eq_ext 0 ls (app l1 l2))).
    split.
    + rewrite Zlength_app.
      lia.
    + intros k Hk.
      rewrite app_Znth1 by lia.
      symmetry.
      apply H6.
      lia.
Qed.

Lemma proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_split_to_missing_i src_pre i n_pre ls 0); try lia.
  sep_apply (IntArray.full_split_to_missing_i dst_pre i n_pre (app l1 l2) 0); try lia.
  replace (Znth i (app l1 l2) 0) with (Znth i ld 0).
  entailer!.
  rewrite app_Znth2 by lia.
  replace (i - Zlength l1) with 0 by lia.
  rewrite H6 by lia.
  replace (i + 0) with i by lia.
  reflexivity.
Qed.

Lemma proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hlen_l1 : Zlength l1 = i) by lia.
  assert (Hprefix_all :
    forall k : Z, 0 <= k < i -> Znth k l1 0 = Znth k ls 0).
  {
    intros k Hk.
    match goal with
    | H : forall k0 : Z, 0 <= k0 < i -> Znth k0 l1 0 = Znth k0 ls 0
      |- _ =>
        apply H; exact Hk
    end.
  }
  assert (Hsuffix_all :
    forall k : Z, 0 <= k < n_pre - i -> Znth k l2 0 = Znth (i + k) ld 0).
  {
    intros k Hk.
    match goal with
    | H : forall k0 : Z, 0 <= k0 < n_pre - i -> Znth k0 l2 0 = Znth (i + k0) ld 0
      |- _ =>
        apply H; exact Hk
    end.
  }
  assert (l2 = sublist i n_pre ld) as Hl2.
  {
    apply (proj2 (list_eq_ext 0 l2 (sublist i n_pre ld))).
    split.
    - rewrite Zlength_sublist by lia.
      lia.
    - intros k Hk.
      rewrite (Znth_sublist i k n_pre ld 0) by lia.
      assert (0 <= k < n_pre - i) as Hrange by lia.
      pose proof (Hsuffix_all k Hrange) as Hsuffix.
      replace (k + i) with (i + k) by lia.
      exact Hsuffix.
  }
  subst l2.
  Exists (l1 ++ cons (Znth i ls 0) nil).
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  rewrite replace_Znth_app_r by lia.
  rewrite Hlen_l1.
  replace (i - i) with 0 by lia.
  rewrite (sublist_split i n_pre (i + 1) ld) by (pose proof (Zlength_correct ld); lia).
  rewrite (sublist_single i ld 0) by (pose proof (Zlength_correct ld); lia).
  simpl.
  assert (forall (l : list Z) (z : Z), replace_nth (length l) z l = l) as Hreplace_nth_len.
  {
    intros l z.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  assert (replace_Znth i (Znth i ls 0) l1 = l1) as Hprefix_keep.
  {
    unfold replace_Znth.
    rewrite Zlength_correct in Hlen_l1.
    replace (Z.to_nat i) with (length l1) by lia.
    apply Hreplace_nth_len.
  }
  assert (
    replace_Znth 0 (Znth i ls 0)
      (Znth i ld 0 :: sublist (i + 1) n_pre ld) =
    Znth i ls 0 :: sublist (i + 1) n_pre ld
  ) as Hhead_write.
  {
    reflexivity.
  }
  simpl.
  rewrite Hprefix_keep.
  rewrite Hhead_write.
  rewrite <- app_assoc.
  simpl.
  entailer!.
  - intros k Hk.
    assert (k < i \/ k = i) as Hcase by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite Hlen_l1; lia).
      apply Hprefix_all.
      lia.
    + subst k.
      rewrite app_Znth2 by (rewrite Hlen_l1; lia).
      rewrite Hlen_l1.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in Hlen_l1.
    rewrite Nat2Z.inj_add.
    rewrite Hlen_l1.
    lia.
Qed.
