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
From SimpleC.EE.CAV.verify_20260422_224852_string_collapse_spaces Require Import string_collapse_spaces_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_collapse_spaces.
Local Open Scope sac.
Local Close Scope sac.
Import ListNotations.

Lemma sccs_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros T l; induction l; intros i v; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; auto.
Qed.

Lemma sccs_replace_Znth_length:
  forall (l: list Z) i v,
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite sccs_replace_nth_length.
  reflexivity.
Qed.

Lemma sccs_replace_Znth_at_app:
  forall (prefix suffix: list Z) v,
    suffix <> nil ->
    replace_Znth (Zlength prefix) v (prefix ++ suffix) =
    prefix ++ v :: tl suffix.
Proof.
  intros prefix suffix v Hsuffix.
  destruct suffix.
  - contradiction.
  - rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (Zlength prefix - Zlength prefix) with 0 by lia.
    simpl.
    reflexivity.
Qed.

Fixpoint sccs_end_space (b: bool) (xs: list Z) : bool :=
  match xs with
  | nil => b
  | x :: xs' =>
      if Z.eq_dec x 32 then sccs_end_space true xs'
      else sccs_end_space false xs'
  end.

Lemma sccs_go_snoc:
  forall b xs x,
    string_collapse_spaces_go b (xs ++ x :: nil) =
    string_collapse_spaces_go b xs ++
      (if Z.eq_dec x 32 then
         if sccs_end_space b xs then nil else 32 :: nil
       else x :: nil).
Proof.
  intros b xs.
  revert b.
  induction xs; intros b x; simpl.
  - destruct (Z.eq_dec x 32); destruct b; simpl; try congruence; reflexivity.
  - destruct (Z.eq_dec a 32); destruct b; simpl; rewrite IHxs; reflexivity.
Qed.

Lemma sccs_end_space_false_last_not:
  forall xs,
    (xs = nil \/ last xs 0 <> 32) ->
    sccs_end_space false xs = false.
Proof.
  induction xs; intros Hlast; simpl.
  - reflexivity.
  - destruct xs.
    + destruct Hlast as [Hnil | Hlast].
      * discriminate.
      * simpl in Hlast. destruct (Z.eq_dec a 32); [congruence | reflexivity].
    + destruct (Z.eq_dec a 32).
      * apply IHxs. right. destruct Hlast as [Hnil | Hlast]; [discriminate | exact Hlast].
      * apply IHxs. right. destruct Hlast as [Hnil | Hlast]; [discriminate | exact Hlast].
Qed.

Lemma sccs_end_space_true_last:
  forall xs,
    xs <> nil ->
    last xs 0 = 32 ->
    sccs_end_space false xs = true.
Proof.
  induction xs; intros Hnonempty Hlast; simpl.
  - contradiction.
  - destruct xs.
    + simpl in Hlast. subst a. destruct (Z.eq_dec 32 32); [reflexivity | congruence].
    + destruct (Z.eq_dec a 32).
      * apply IHxs; [discriminate | exact Hlast].
      * apply IHxs; [discriminate | exact Hlast].
Qed.

Lemma sccs_spec_snoc_nonspace:
  forall xs x,
    x <> 32 ->
    string_collapse_spaces_spec (xs ++ x :: nil) =
    string_collapse_spaces_spec xs ++ x :: nil.
Proof.
  intros xs x Hx.
  unfold string_collapse_spaces_spec.
  rewrite sccs_go_snoc.
  destruct (Z.eq_dec x 32); congruence.
Qed.

Lemma sccs_spec_snoc_space_emit:
  forall xs,
    (xs = nil \/ last xs 0 <> 32) ->
    string_collapse_spaces_spec (xs ++ 32 :: nil) =
    string_collapse_spaces_spec xs ++ 32 :: nil.
Proof.
  intros xs Hlast.
  unfold string_collapse_spaces_spec.
  rewrite sccs_go_snoc.
  destruct (Z.eq_dec 32 32) as [_ | Hbad].
  - rewrite sccs_end_space_false_last_not by exact Hlast.
    reflexivity.
  - congruence.
Qed.

Lemma sccs_spec_snoc_space_suppress:
  forall xs,
    xs <> nil ->
    last xs 0 = 32 ->
    string_collapse_spaces_spec (xs ++ 32 :: nil) =
    string_collapse_spaces_spec xs.
Proof.
  intros xs Hnonempty Hlast.
  unfold string_collapse_spaces_spec.
  rewrite sccs_go_snoc.
  destruct (Z.eq_dec 32 32) as [_ | Hbad].
  - rewrite sccs_end_space_true_last by (assumption || reflexivity).
    rewrite app_nil_r.
    reflexivity.
  - congruence.
Qed.

Lemma sccs_last_Znth:
  forall (xs: list Z) d,
    xs <> nil ->
    last xs d = Znth (Zlength xs - 1) xs d.
Proof.
  intros xs.
  induction xs using rev_ind; intros d Hnonempty.
  - contradiction.
  - rewrite last_last.
    rewrite Zlength_app_cons.
    replace (Zlength xs + 1 - 1) with (Zlength xs) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength xs - Zlength xs) with 0 by lia.
    simpl.
    reflexivity.
Qed.

Lemma sccs_spec_snoc_space_emit_by_Znth:
  forall xs,
    Zlength xs = 0 \/
      (0 < Zlength xs /\ Znth (Zlength xs - 1) xs 0 <> 32) ->
    string_collapse_spaces_spec (xs ++ 32 :: nil) =
    string_collapse_spaces_spec xs ++ 32 :: nil.
Proof.
  intros xs Hprev.
  apply sccs_spec_snoc_space_emit.
  destruct Hprev as [Hzero | [Hpos Hlast]].
  - left.
    destruct xs.
    + reflexivity.
    + rewrite Zlength_cons in Hzero.
      pose proof (Zlength_nonneg xs).
      lia.
  - right.
    rewrite sccs_last_Znth with (d := 0) by
      (intro Hnil; subst; rewrite Zlength_nil in Hpos; lia).
    exact Hlast.
Qed.

Lemma sccs_spec_snoc_space_suppress_by_Znth:
  forall xs,
    0 < Zlength xs ->
    Znth (Zlength xs - 1) xs 0 = 32 ->
    string_collapse_spaces_spec (xs ++ 32 :: nil) =
    string_collapse_spaces_spec xs.
Proof.
  intros xs Hpos Hlast.
  apply sccs_spec_snoc_space_suppress.
  - intro Hnil; subst; rewrite Zlength_nil in Hpos; lia.
  - rewrite sccs_last_Znth with (d := 0) by
      (intro Hnil; subst; rewrite Zlength_nil in Hpos; lia).
    exact Hlast.
Qed.

Local Open Scope sac.

Lemma proof_of_string_collapse_spaces_entail_wit_1 : string_collapse_spaces_entail_wit_1.
Proof.
  unfold string_collapse_spaces_entail_wit_1.
  pre_process.
  Exists d.
  Exists (@nil Z).
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_string_collapse_spaces_entail_wit_2_1 : string_collapse_spaces_entail_wit_2_1.
Proof.
  unfold string_collapse_spaces_entail_wit_2_1.
  pre_process.
  prop_apply CharArray.full_length.
  Intros.
  assert (Hi_lt_n: i < n).
  {
    destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq].
    - subst i.
      rewrite app_Znth2 in H0 by lia.
      rewrite H11 in H0.
      replace (Zlength lin_2 - n) with 0 in H0 by lia.
      simpl in H0.
      inversion H0.
    - lia.
  }
  destruct lrest_2 eqn:Hlrest.
  {
    subst l.
    rewrite Zlength_app in H11.
    rewrite Zlength_nil in H11.
    lia.
  }
  rename z into cur.
  rename l0 into xs.
  assert (Hcur: cur = 32).
  {
    rewrite app_Znth1 in H0 by lia.
    rewrite H9 in H0.
    rewrite app_Znth2 in H0 by lia.
    rewrite H10 in H0.
    replace (i - i) with 0 in H0 by lia.
    simpl in H0.
    exact H0.
  }
  subst cur.
  assert (Hdout_len: 0 < Zlength dout_2).
  {
    assert (Hout_len:
      Zlength (replace_Znth j 32 (string_collapse_spaces_spec lin_2 ++ dout_2)) =
      n + 1).
    {
      rewrite Zlength_correct.
      exact H20.
    }
    rewrite sccs_replace_Znth_length in Hout_len.
    rewrite Zlength_app in Hout_len.
    rewrite <- H12 in Hout_len.
    pose proof (Zlength_nonneg dout_2).
    lia.
  }
  destruct dout_2 eqn:Hdout.
  {
    rewrite Zlength_nil in Hdout_len.
    lia.
  }
  rename z into y.
  rename l0 into ys.
  assert (Hemit:
    string_collapse_spaces_spec (lin_2 ++ 32 :: nil) =
    string_collapse_spaces_spec lin_2 ++ 32 :: nil).
  {
    apply sccs_spec_snoc_space_emit_by_Znth.
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    - left. lia.
    - right.
      split.
      + lia.
      + assert (Hprev_l: Znth (i - 1) l 0 <> 32).
        {
          apply H13.
          split; [exact H | lia].
        }
        rewrite H9 in Hprev_l.
        rewrite app_Znth1 in Hprev_l by lia.
        rewrite H10.
        exact Hprev_l.
  }
  assert (Hreplace:
    replace_Znth j 32 (string_collapse_spaces_spec lin_2 ++ y :: ys) =
    string_collapse_spaces_spec (lin_2 ++ 32 :: nil) ++ ys).
  {
    rewrite H12.
    rewrite sccs_replace_Znth_at_app by discriminate.
    rewrite Hemit.
    rewrite <- app_assoc.
    reflexivity.
  }
  assert (Hsplit_next: l = (lin_2 ++ 32 :: nil) ++ xs).
  {
    rewrite H9.
    rewrite <- app_assoc.
    reflexivity.
  }
  assert (Hlen_next: Zlength (lin_2 ++ 32 :: nil) = i + 1).
  {
    rewrite Zlength_app_cons.
    lia.
  }
  assert (Hj_next:
    j + 1 = Zlength (string_collapse_spaces_spec (lin_2 ++ 32 :: nil))).
  {
    rewrite Hemit.
    rewrite Zlength_app_cons.
    lia.
  }
  rewrite Hreplace.
  Exists ys.
  Exists (lin_2 ++ 32 :: nil).
  Exists xs.
  rewrite Hsplit_next.
  entailer!; try lia.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H15.
    exact Hk.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H19.
    exact Hk.
  - intros _.
    split.
    + lia.
    + replace (i + 1 - 1) with i by lia.
      rewrite app_Znth1 by (rewrite Hlen_next; lia).
      rewrite app_Znth2 by lia.
      rewrite H10.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite <- Hsplit_next.
    exact H11.
  - rewrite <- Hsplit_next.
    exact H18.
Qed. 

Lemma proof_of_string_collapse_spaces_entail_wit_2_2 : string_collapse_spaces_entail_wit_2_2.
Proof.
  unfold string_collapse_spaces_entail_wit_2_2.
  pre_process.
  assert (Hin_one: in_space = 1) by lia.
  assert (Hi_lt_n: i < n).
  {
    destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq].
    - subst i.
      rewrite app_Znth2 in H0 by lia.
      rewrite H11 in H0.
      replace (Zlength lin_2 - n) with 0 in H0 by lia.
      simpl in H0.
      inversion H0.
    - lia.
  }
  destruct lrest_2 eqn:Hlrest.
  {
    subst l.
    rewrite Zlength_app in H11.
    rewrite Zlength_nil in H11.
    lia.
  }
  rename z into cur.
  rename l0 into xs.
  assert (Hcur: cur = 32).
  {
    rewrite app_Znth1 in H0 by lia.
    rewrite H9 in H0.
    rewrite app_Znth2 in H0 by lia.
    rewrite H10 in H0.
    replace (i - i) with 0 in H0 by lia.
    simpl in H0.
    exact H0.
  }
  subst cur.
  assert (Hsuppress:
    string_collapse_spaces_spec (lin_2 ++ 32 :: nil) =
    string_collapse_spaces_spec lin_2).
  {
    apply sccs_spec_snoc_space_suppress_by_Znth.
    - pose proof (H14 Hin_one) as [Hpos _].
      lia.
    - pose proof (H14 Hin_one) as [_ Hprev_l].
      rewrite H9 in Hprev_l.
      rewrite app_Znth1 in Hprev_l by lia.
      rewrite H10.
      exact Hprev_l.
  }
  assert (Hsplit_next: l = (lin_2 ++ 32 :: nil) ++ xs).
  {
    rewrite H9.
    rewrite <- app_assoc.
    reflexivity.
  }
  assert (Hlen_next: Zlength (lin_2 ++ 32 :: nil) = i + 1).
  {
    rewrite Zlength_app_cons.
    lia.
  }
  assert (Hj_next:
    j = Zlength (string_collapse_spaces_spec (lin_2 ++ 32 :: nil))).
  {
    rewrite Hsuppress.
    exact H12.
  }
  rewrite <- Hsuppress.
  Exists dout_2.
  Exists (lin_2 ++ 32 :: nil).
  Exists xs.
  rewrite Hsplit_next.
  entailer!; try lia.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H15.
    exact Hk.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H19.
    exact Hk.
  - intros _.
    split.
    + lia.
    + replace (i + 1 - 1) with i by lia.
      rewrite app_Znth1 by (rewrite Hlen_next; lia).
      rewrite app_Znth2 by lia.
      rewrite H10.
      replace (i - i) with 0 by lia.
      simpl.
      reflexivity.
  - rewrite <- Hsplit_next.
    exact H11.
  - rewrite <- Hsplit_next.
    exact H18.
Qed. 

Lemma proof_of_string_collapse_spaces_entail_wit_2_3 : string_collapse_spaces_entail_wit_2_3.
Proof.
  unfold string_collapse_spaces_entail_wit_2_3.
  pre_process.
  prop_apply CharArray.full_length.
  Intros.
  assert (Hi_lt_n: i < n).
  {
    destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq].
    - subst i.
      rewrite app_Znth2 in H0 by lia.
      rewrite H10 in H0.
      replace (Zlength lin_2 - n) with 0 in H0 by lia.
      simpl in H0.
      contradiction.
    - lia.
  }
  destruct lrest_2 eqn:Hlrest.
  {
    subst l.
    rewrite Zlength_app in H10.
    rewrite Zlength_nil in H10.
    lia.
  }
  rename z into cur.
  rename l0 into xs.
  assert (Hread: Znth i (l ++ 0 :: nil) 0 = cur).
  {
    rewrite app_Znth1 by lia.
    rewrite H8.
    rewrite app_Znth2 by lia.
    rewrite H9.
    replace (i - i) with 0 by lia.
    simpl.
    reflexivity.
  }
  assert (Hcur_nonspace: cur <> 32).
  {
    rewrite <- Hread.
    exact H.
  }
  assert (Hdout_len: 0 < Zlength dout_2).
  {
    assert (Hout_len:
      Zlength (replace_Znth j (Znth i (l ++ 0 :: nil) 0)
        (string_collapse_spaces_spec lin_2 ++ dout_2)) =
      n + 1).
    {
      rewrite Zlength_correct.
      exact H19.
    }
    rewrite sccs_replace_Znth_length in Hout_len.
    rewrite Zlength_app in Hout_len.
    rewrite <- H11 in Hout_len.
    pose proof (Zlength_nonneg dout_2).
    lia.
  }
  destruct dout_2 eqn:Hdout.
  {
    rewrite Zlength_nil in Hdout_len.
    lia.
  }
  rename z into y.
  rename l0 into ys.
  assert (Hspec:
    string_collapse_spaces_spec (lin_2 ++ cur :: nil) =
    string_collapse_spaces_spec lin_2 ++ cur :: nil).
  {
    apply sccs_spec_snoc_nonspace.
    exact Hcur_nonspace.
  }
  assert (Hreplace:
    replace_Znth j (Znth i (l ++ 0 :: nil) 0)
      (string_collapse_spaces_spec lin_2 ++ y :: ys) =
    string_collapse_spaces_spec (lin_2 ++ cur :: nil) ++ ys).
  {
    rewrite Hread.
    rewrite H11.
    rewrite sccs_replace_Znth_at_app by discriminate.
    rewrite Hspec.
    rewrite <- app_assoc.
    reflexivity.
  }
  assert (Hsplit_next: l = (lin_2 ++ cur :: nil) ++ xs).
  {
    rewrite H8.
    rewrite <- app_assoc.
    reflexivity.
  }
  assert (Hlen_next: Zlength (lin_2 ++ cur :: nil) = i + 1).
  {
    rewrite Zlength_app_cons.
    lia.
  }
  assert (Hj_next:
    j + 1 = Zlength (string_collapse_spaces_spec (lin_2 ++ cur :: nil))).
  {
    rewrite Hspec.
    rewrite Zlength_app_cons.
    lia.
  }
  rewrite Hreplace.
  Exists ys.
  Exists (lin_2 ++ cur :: nil).
  Exists xs.
  rewrite Hsplit_next.
  entailer!; try lia.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H14.
    exact Hk.
  - intros k Hk.
    rewrite <- Hsplit_next.
    apply H18.
    exact Hk.
  - intros [_ _].
    replace (i + 1 - 1) with i by lia.
    rewrite app_Znth1 by (rewrite Hlen_next; lia).
    rewrite app_Znth2 by lia.
    rewrite H9.
    replace (i - i) with 0 by lia.
    simpl.
    exact Hcur_nonspace.
  - rewrite <- Hsplit_next.
    exact H10.
  - rewrite <- Hsplit_next.
    exact H17.
Qed. 

Lemma proof_of_string_collapse_spaces_return_wit_1 : string_collapse_spaces_return_wit_1.
Proof.
  unfold string_collapse_spaces_return_wit_1.
  pre_process.
  prop_apply CharArray.full_length.
  Intros.
  assert (Hi_eq_n: i = n).
  {
    destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq].
    - exact Hi_eq.
    - assert (Hi_lt_n: i < n) by lia.
      rewrite app_Znth1 in H by lia.
      pose proof (H13 i) as Hnozero.
      specialize (Hnozero ltac:(lia)).
      congruence.
  }
  subst i.
  assert (Hlrest_len: Zlength lrest = 0).
  {
    rewrite H7 in H9.
    rewrite Zlength_app in H9.
    lia.
  }
  destruct lrest eqn:Hlrest.
  2: {
    rename z into rest_head.
    rename l0 into rest_tail.
    rewrite Zlength_cons in Hlrest_len.
    pose proof (Zlength_nonneg rest_tail).
    lia.
  }
  rewrite app_nil_r in H7.
  subst l.
  assert (Hdout_len: 0 < Zlength dout).
  {
    assert (Hout_len:
      Zlength (replace_Znth j 0 (string_collapse_spaces_spec lin ++ dout)) =
      n + 1).
    {
      rewrite Zlength_correct.
      exact H18.
    }
    rewrite sccs_replace_Znth_length in Hout_len.
    rewrite Zlength_app in Hout_len.
    rewrite <- H10 in Hout_len.
    pose proof (Zlength_nonneg dout).
    lia.
  }
  destruct dout eqn:Hdout.
  {
    rewrite Zlength_nil in Hdout_len.
    lia.
  }
  rename z into y.
  rename l into t.
  assert (Hreplace:
    replace_Znth j 0 (string_collapse_spaces_spec lin ++ y :: t) =
    (string_collapse_spaces_spec lin ++ 0 :: nil) ++ t).
  {
    rewrite H10.
    rewrite sccs_replace_Znth_at_app by discriminate.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hreplace.
  Exists t.
  entailer!; try lia.
  assert (Hout_len:
    Zlength (replace_Znth j 0 (string_collapse_spaces_spec lin ++ y :: t)) =
    n + 1).
  {
    rewrite Zlength_correct.
    exact H18.
  }
  rewrite sccs_replace_Znth_length in Hout_len.
  rewrite Zlength_app in Hout_len.
  rewrite <- H10 in Hout_len.
  rewrite Zlength_cons in Hout_len.
  lia.
Qed. 
