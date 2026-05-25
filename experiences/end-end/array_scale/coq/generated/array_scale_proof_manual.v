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
From SimpleC.EE.CAV.verify_20260422_080741_array_scale Require Import array_scale_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_scale_safety_wit_2 : array_scale_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  - pose proof (H11 i ltac:(lia)) as Hrange.
    lia.
  - pose proof (H11 i ltac:(lia)) as Hrange.
    lia.
Qed.

Lemma proof_of_array_scale_entail_wit_1 : array_scale_entail_wit_1.
Proof.
  pre_process.
  Exists lo.
  Exists (@nil Z).
  entailer!.
Qed.

Lemma proof_of_array_scale_entail_wit_2 : array_scale_entail_wit_2.
Proof.
  pre_process.
  assert (l2_2 = sublist i_2 n_pre lo) as Hl2.
  {
    apply (proj2 (list_eq_ext 0 l2_2 (sublist i_2 n_pre lo))).
    split.
    - rewrite Zlength_sublist by lia.
      lia.
    - intros t Ht.
      rewrite (Znth_sublist i_2 t n_pre lo 0) by lia.
      assert (0 <= t < n_pre - i_2) as Hrange.
      {
        rewrite <- H5.
        exact Ht.
      }
      pose proof (H7 t Hrange) as Hsuffix.
      replace (t + i_2) with (i_2 + t) by lia.
      exact Hsuffix.
  }
  subst l2_2.
  Exists (sublist (i_2 + 1) n_pre lo).
  Exists (l1_2 ++ cons (Znth i_2 la 0 * k_pre) nil).
  rewrite replace_Znth_app_r by lia.
  rewrite H4.
  replace (i_2 - i_2) with 0 by lia.
  rewrite (sublist_split i_2 n_pre (i_2 + 1) lo) by (pose proof (Zlength_correct lo); lia).
  rewrite (sublist_single i_2 lo 0) by (pose proof (Zlength_correct lo); lia).
  simpl.
  assert (forall (l : list Z) (z : Z), replace_nth (length l) z l = l) as Hreplace_nth_len.
  {
    intros l z.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  assert (replace_Znth i_2 (Znth i_2 la 0 * k_pre) l1_2 = l1_2) as Hprefix_keep.
  {
    unfold replace_Znth.
    rewrite Zlength_correct in H4.
    replace (Z.to_nat i_2) with (length l1_2) by lia.
    apply Hreplace_nth_len.
  }
  assert (
    replace_Znth 0 (Znth i_2 la 0 * k_pre)
      (Znth i_2 lo 0 :: sublist (i_2 + 1) n_pre lo) =
    Znth i_2 la 0 * k_pre :: sublist (i_2 + 1) n_pre lo
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
  - intros t Ht.
    rewrite (Znth_sublist (i_2 + 1) t n_pre lo 0) by lia.
    replace (t + (i_2 + 1)) with (i_2 + 1 + t) by lia.
    reflexivity.
  - intros t Ht.
    assert (t < i_2 \/ t = i_2) as Hcase by lia.
    destruct Hcase as [Hlt | Heq].
    + rewrite app_Znth1 by (rewrite H4; lia).
      apply H6.
      lia.
    + subst t.
      rewrite app_Znth2 by (rewrite H4; lia).
      rewrite H4.
      replace (i_2 - i_2) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
  - rewrite Zlength_correct.
    rewrite length_app.
    simpl.
    rewrite Zlength_correct in H4.
    rewrite Nat2Z.inj_add.
    rewrite H4.
    lia.
Qed.

Lemma proof_of_array_scale_return_wit_1 : array_scale_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i_3 = n_pre) by lia.
  subst i_3.
  Exists (app l1 l2).
  entailer!.
  - intros i Hi_range.
    rewrite app_Znth1 by lia.
    apply H6; lia.
  - rewrite Zlength_app.
    lia.
Qed.
