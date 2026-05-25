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
From SimpleC.EE.CAV.verify_20260422_074343_array_reverse_in_place Require Import array_reverse_in_place_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma replace_Znth_boundary_swap :
  forall (p mid s : list Z) (x y : Z),
    replace_Znth (Zlength p + 1 + Zlength mid) x
      (replace_Znth (Zlength p) y (p ++ x :: mid ++ y :: s)) =
    p ++ y :: mid ++ x :: s.
Proof.
  intros.
  pose proof (Zlength_nonneg p).
  pose proof (Zlength_nonneg mid).
  rewrite replace_Znth_app_r by lia.
  rewrite (replace_Znth_nothing (Zlength p) p y) by lia.
  replace (Zlength p - Zlength p) with 0 by lia.
  change (replace_Znth 0 y (x :: mid ++ y :: s)) with (y :: mid ++ y :: s).
  rewrite replace_Znth_app_r.
  2: lia.
  rewrite (replace_Znth_nothing (Zlength p + 1 + Zlength mid) p x) by lia.
  replace (Zlength p + 1 + Zlength mid - Zlength p)
    with (1 + Zlength mid) by lia.
  change (y :: mid ++ y :: s) with ((y :: mid) ++ (y :: s)).
  rewrite replace_Znth_app_r by (rewrite Zlength_cons; lia).
  rewrite (replace_Znth_nothing (1 + Zlength mid) (y :: mid) x)
    by (rewrite Zlength_cons; lia).
  replace (1 + Zlength mid - Zlength (y :: mid)) with 0
    by (rewrite Zlength_cons; lia).
  change (replace_Znth 0 x (y :: s)) with (x :: s).
  reflexivity.
Qed.

Lemma reverse_step_current_decomp :
  forall (l : list Z) n left right,
    Zlength l = n ->
    0 <= left ->
    left < right ->
    right = n - 1 - left ->
    rev (sublist (n - left) n l) ++
      sublist left (right + 1) l ++
      rev (sublist 0 left l) =
    rev (sublist (n - left) n l) ++
      Znth left l 0 :: sublist (left + 1) right l ++
      Znth right l 0 :: rev (sublist 0 left l).
Proof.
  intros l n left right Hlen Hleft Hlt Hright.
  rewrite (sublist_split left (right + 1) (left + 1) l)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite (sublist_single left l 0)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite (sublist_split (left + 1) (right + 1) right l)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite (sublist_single right l 0)
    by (rewrite Zlength_correct in Hlen; lia).
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma reverse_step_target_decomp :
  forall (l : list Z) n left right,
    Zlength l = n ->
    0 <= left ->
    left < right ->
    right = n - 1 - left ->
    rev (sublist (n - (left + 1)) n l) ++
      sublist (left + 1) (right - 1 + 1) l ++
      rev (sublist 0 (left + 1) l) =
    rev (sublist (n - left) n l) ++
      Znth right l 0 :: sublist (left + 1) right l ++
      Znth left l 0 :: rev (sublist 0 left l).
Proof.
  intros l n left right Hlen Hleft Hlt Hright.
  replace (n - (left + 1)) with right by lia.
  replace (right - 1 + 1) with right by lia.
  rewrite (sublist_split right n (right + 1) l)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite (sublist_single right l 0)
    by (rewrite Zlength_correct in Hlen; lia).
  replace (right + 1) with (n - left) by lia.
  rewrite rev_app_distr.
  simpl.
  rewrite (sublist_split 0 (left + 1) left l)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite (sublist_single left l 0)
    by (rewrite Zlength_correct in Hlen; lia).
  rewrite rev_app_distr.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma reverse_exit_decomp :
  forall (l : list Z) n left right,
    Zlength l = n ->
    0 <= left ->
    left <= n ->
    left >= right ->
    left <= right + 1 ->
    right = n - 1 - left ->
    rev (sublist (n - left) n l) ++
      sublist left (right + 1) l ++
      rev (sublist 0 left l) =
    rev l.
Proof.
  intros l n left right Hlen Hleft Hle_n Hge Hcross Hright.
  assert (Hcase : left = right \/ left = right + 1) by lia.
  destruct Hcase as [Heq | Heq].
  - subst right.
    replace (n - left) with (left + 1) by lia.
    replace (n - 1 - left + 1) with (left + 1) by lia.
    replace (rev l) with
      (rev (sublist (left + 1) n l) ++
       sublist left (left + 1) l ++
       rev (sublist 0 left l)).
    2: {
      assert (Hsplit :
        l = sublist 0 left l ++ sublist left (left + 1) l ++ sublist (left + 1) n l).
      {
        rewrite <- (sublist_split left n (left + 1) l)
          by (rewrite Zlength_correct in Hlen; lia).
        rewrite <- (sublist_split 0 n left l)
          by (rewrite Zlength_correct in Hlen; lia).
        rewrite sublist_self by (symmetry; exact Hlen).
        reflexivity.
      }
      rewrite (f_equal (@rev Z) Hsplit).
      repeat rewrite rev_app_distr.
      rewrite (sublist_single left l 0)
        by (rewrite Zlength_correct in Hlen; lia).
      simpl.
      repeat rewrite <- app_assoc.
      reflexivity.
    }
    reflexivity.
  - subst left.
    replace (n - (right + 1)) with (right + 1) by lia.
    rewrite (sublist_nil l (right + 1) (right + 1)) by lia.
    simpl.
    replace (rev l) with
      (rev (sublist (right + 1) n l) ++ rev (sublist 0 (right + 1) l)).
    2: {
      assert (Hsplit :
        l = sublist 0 (right + 1) l ++ sublist (right + 1) n l).
      {
        rewrite <- (sublist_split 0 n (right + 1) l)
          by (rewrite Zlength_correct in Hlen; lia).
        rewrite sublist_self by (symmetry; exact Hlen).
        reflexivity.
      }
      rewrite (f_equal (@rev Z) Hsplit).
      rewrite rev_app_distr.
      reflexivity.
    }
    reflexivity.
Qed.

Lemma proof_of_array_reverse_in_place_entail_wit_1 : array_reverse_in_place_entail_wit_1.
Proof.
  pre_process.
  replace (n_pre - 0) with n_pre by lia.
  replace ((n_pre - 1) + 1) with n_pre by lia.
  rewrite sublist_nil by lia.
  rewrite sublist_self by (symmetry; exact H0).
  simpl.
  rewrite app_nil_r.
  entailer!.
Qed. 

Lemma proof_of_array_reverse_in_place_entail_wit_2 : array_reverse_in_place_entail_wit_2.
Proof.
  pre_process.
  set (cur :=
    rev (sublist (n_pre - left) n_pre l) ++
    sublist left (right + 1) l ++
    rev (sublist 0 left l)).
  set (p := rev (sublist (n_pre - left) n_pre l)).
  set (mid := sublist (left + 1) right l).
  set (s := rev (sublist 0 left l)).
  set (x := Znth left l 0).
  set (y := Znth right l 0).
  assert (Hcur : cur = p ++ x :: mid ++ y :: s).
  {
    subst cur p mid s x y.
    apply reverse_step_current_decomp; lia.
  }
  assert (Hp_len : Zlength p = left).
  {
    subst p.
    rewrite Zlength_correct, rev_length.
    rewrite <- Zlength_correct.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hmid_len : Zlength mid = right - left - 1).
  {
    subst mid.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hleft_val : Znth left cur 0 = x).
  {
    rewrite Hcur.
    rewrite app_Znth2 by lia.
    replace (left - Zlength p) with 0 by lia.
    simpl.
    reflexivity.
  }
  assert (Hright_val : Znth right cur 0 = y).
  {
    rewrite Hcur.
    rewrite app_Znth2 by lia.
    replace (right - Zlength p) with (1 + Zlength mid) by lia.
    rewrite Znth_cons by lia.
    replace (1 + Zlength mid - 1) with (Zlength mid) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength mid - Zlength mid) with 0 by lia.
    simpl.
    reflexivity.
  }
  assert (Htarget :
    rev (sublist (n_pre - (left + 1)) n_pre l) ++
      sublist (left + 1) (right - 1 + 1) l ++
      rev (sublist 0 (left + 1) l) =
    p ++ y :: mid ++ x :: s).
  {
    subst p mid s x y.
    apply reverse_step_target_decomp; lia.
  }
  fold cur.
  rewrite Hleft_val, Hright_val.
  rewrite Hcur.
  replace (replace_Znth right x (replace_Znth left y (p ++ x :: mid ++ y :: s)))
    with (p ++ y :: mid ++ x :: s).
  2: {
    replace left with (Zlength p) by lia.
    replace right with (Zlength p + 1 + Zlength mid) by lia.
    symmetry.
    apply replace_Znth_boundary_swap.
  }
  rewrite Htarget.
  entailer!.
Qed. 

Lemma proof_of_array_reverse_in_place_return_wit_1 : array_reverse_in_place_return_wit_1.
Proof.
  pre_process.
  rewrite (reverse_exit_decomp l n_pre left right) by lia.
  entailer!.
Qed. 
