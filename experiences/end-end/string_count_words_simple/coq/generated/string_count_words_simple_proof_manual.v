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
From SimpleC.EE.CAV.verify_20260423_014132_string_count_words_simple Require Import string_count_words_simple_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_words_simple.
Local Open Scope sac.

Lemma sublist_prefix_snoc_Z :
  forall {A : Type} (l : list A) (i : Z) (d : A),
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A l i d Hi.
  rewrite (sublist_split 0 (i + 1) i l)
    by (pose proof (Zlength_correct l); lia).
  rewrite (sublist_single i l d) by (pose proof (Zlength_correct l); lia).
  reflexivity.
Qed.

Lemma string_count_words_simple_go_app_space :
  forall (b : bool) (l : list Z),
    string_count_words_simple_go b (l ++ 32 :: nil) =
    string_count_words_simple_go b l.
Proof.
  intros b l.
  revert b.
  induction l; intros b.
  - simpl. destruct b; destruct (Z.eq_dec 32 32); lia.
  - simpl.
    destruct (Z.eq_dec a 32).
    + apply (IHl false).
    + destruct b.
      * apply (IHl true).
      * change (1 + string_count_words_simple_go true (l ++ 32 :: nil) =
                1 + string_count_words_simple_go true l).
        rewrite (IHl true). lia.
Qed.

Lemma string_count_words_simple_spec_app_space :
  forall (l : list Z),
    string_count_words_simple_spec (l ++ 32 :: nil) =
    string_count_words_simple_spec l.
Proof.
  intros l.
  unfold string_count_words_simple_spec.
  apply string_count_words_simple_go_app_space.
Qed.

Lemma string_count_words_simple_spec_single_nonspace :
  forall x : Z,
    x <> 32 ->
    string_count_words_simple_spec (x :: nil) =
    string_count_words_simple_spec nil + 1.
Proof.
  intros x Hx.
  unfold string_count_words_simple_spec.
  simpl.
  destruct (Z.eq_dec x 32); lia.
Qed.

Lemma string_count_words_simple_go_app_space_nonspace :
  forall (b : bool) (l : list Z) (x : Z),
    x <> 32 ->
    string_count_words_simple_go b ((l ++ 32 :: nil) ++ x :: nil) =
    string_count_words_simple_go b (l ++ 32 :: nil) + 1.
Proof.
  intros b l x Hx.
  revert b.
  induction l.
  - intros b.
    simpl.
    destruct b; destruct (Z.eq_dec x 32); lia.
  - intros b.
    simpl.
    destruct (Z.eq_dec a 32).
    + apply (IHl false).
    + destruct b.
      * apply (IHl true).
      * change (1 + string_count_words_simple_go true ((l ++ 32 :: nil) ++ x :: nil) =
                1 + string_count_words_simple_go true (l ++ 32 :: nil) + 1).
        rewrite (IHl true). lia.
Qed.

Lemma string_count_words_simple_spec_app_space_nonspace :
  forall (l : list Z) (x : Z),
    x <> 32 ->
    string_count_words_simple_spec ((l ++ 32 :: nil) ++ x :: nil) =
    string_count_words_simple_spec (l ++ 32 :: nil) + 1.
Proof.
  intros l x Hx.
  unfold string_count_words_simple_spec.
  apply string_count_words_simple_go_app_space_nonspace.
  exact Hx.
Qed.

Lemma string_count_words_simple_go_app_nonspace_nonspace :
  forall (b : bool) (l : list Z) (y x : Z),
    y <> 32 ->
    x <> 32 ->
    string_count_words_simple_go b ((l ++ y :: nil) ++ x :: nil) =
    string_count_words_simple_go b (l ++ y :: nil).
Proof.
  intros b l y x Hy Hx.
  revert b.
  induction l.
  - intros b.
    simpl.
    destruct (Z.eq_dec y 32).
    + lia.
    + destruct b; destruct (Z.eq_dec x 32); lia.
  - intros b.
    simpl.
    destruct (Z.eq_dec a 32).
    + apply IHl.
    + destruct b; rewrite IHl; lia.
Qed.

Lemma string_count_words_simple_spec_app_nonspace_nonspace :
  forall (l : list Z) (y x : Z),
    y <> 32 ->
    x <> 32 ->
    string_count_words_simple_spec ((l ++ y :: nil) ++ x :: nil) =
    string_count_words_simple_spec (l ++ y :: nil).
Proof.
  intros l y x Hy Hx.
  unfold string_count_words_simple_spec.
  apply string_count_words_simple_go_app_nonspace_nonspace; assumption.
Qed.

Lemma proof_of_string_count_words_simple_entail_wit_1 : string_count_words_simple_entail_wit_1.
Proof.
  unfold string_count_words_simple_entail_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_string_count_words_simple_entail_wit_2_1 : string_count_words_simple_entail_wit_2_1.
Proof.
  unfold string_count_words_simple_entail_wit_2_1.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H.
      rewrite app_Znth2 in H by lia.
      replace (n - Zlength l) with 0 in H by lia.
      simpl in H.
      discriminate H.
  }
  assert (Hcur_space : Znth i l 0 = 32).
  {
    rewrite app_Znth1 in H by lia.
    exact H.
  }
  assert (Hprefix :
    sublist 0 (i + 1) l = sublist 0 i l ++ 32 :: nil).
  {
    rewrite (sublist_prefix_snoc_Z l i 0) by lia.
    rewrite Hcur_space.
    reflexivity.
  }
  rewrite Hprefix.
  rewrite string_count_words_simple_spec_app_space.
  entailer!; try lia.
  intros _.
  replace (i + 1 - 1) with i by lia.
  exact Hcur_space.
Qed.

Lemma proof_of_string_count_words_simple_entail_wit_2_2 : string_count_words_simple_entail_wit_2_2.
Proof.
  unfold string_count_words_simple_entail_wit_2_2.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H1.
      rewrite app_Znth2 in H1 by lia.
      replace (n - Zlength l) with 0 in H1 by lia.
      simpl in H1.
      exfalso.
      apply H1.
      reflexivity.
  }
  assert (Hcur_nonspace : Znth i l 0 <> 32).
  {
    rewrite app_Znth1 in H0 by lia.
    exact H0.
  }
  assert (Hprefix_next :
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l 0 :: nil).
  {
    apply sublist_prefix_snoc_Z.
    lia.
  }
  destruct (Z.eq_dec i 0) as [Hi0 | Hine0].
  - subst i.
    rewrite Hprefix_next.
    rewrite sublist_nil by lia.
    rewrite sublist_nil in H9 by lia.
    simpl.
    simpl in H9.
    rewrite string_count_words_simple_spec_single_nonspace by exact Hcur_nonspace.
    assert (Hnext_in_word :
      1 = 1 -> 0 < 0 + 1 /\ Znth (0 + 1 - 1) l 0 <> 32).
    {
      intros _.
      split.
      * lia.
      * replace (0 + 1 - 1) with 0 by lia.
        exact Hcur_nonspace.
    }
    entailer!; try lia.
  - assert (Hi_pos : 0 < i) by lia.
    assert (Hprev_space : Znth (i - 1) l 0 = 32).
    {
      match goal with
      | Hprev : 0 < i /\ in_word = 0 -> Znth (i - 1) l 0 = 32 |- _ =>
          apply Hprev; split; lia
      end.
    }
    assert (Hprefix_cur :
      sublist 0 i l = sublist 0 (i - 1) l ++ 32 :: nil).
    {
      transitivity (sublist 0 (i - 1) l ++ Znth (i - 1) l 0 :: nil).
      - replace i with ((i - 1) + 1) at 1 by lia.
        apply sublist_prefix_snoc_Z.
        lia.
      - rewrite Hprev_space.
        reflexivity.
    }
    rewrite Hprefix_next.
    rewrite Hprefix_cur.
    rewrite Hprefix_cur in H9.
    rewrite string_count_words_simple_spec_app_space_nonspace
      by exact Hcur_nonspace.
    assert (Hnext_in_word :
      1 = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) l 0 <> 32).
    {
      intros _.
      split.
      * lia.
      * replace (i + 1 - 1) with i by lia.
        exact Hcur_nonspace.
    }
    entailer!; try lia.
Qed.

Lemma proof_of_string_count_words_simple_entail_wit_2_3 : string_count_words_simple_entail_wit_2_3.
Proof.
  unfold string_count_words_simple_entail_wit_2_3.
  pre_process.
  assert (Hin_word_one : in_word = 1) by lia.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H1.
      rewrite app_Znth2 in H1 by lia.
      replace (n - Zlength l) with 0 in H1 by lia.
      simpl in H1.
      exfalso.
      apply H1.
      reflexivity.
  }
  assert (Hcur_nonspace : Znth i l 0 <> 32).
  {
    rewrite app_Znth1 in H0 by lia.
    exact H0.
  }
  assert (Hprev_nonspace : Znth (i - 1) l 0 <> 32).
  {
    match goal with
    | Hprev : in_word = 1 -> 0 < i /\ Znth (i - 1) l 0 <> 32 |- _ =>
        destruct (Hprev Hin_word_one) as [_ Hneq]; exact Hneq
    end.
  }
  assert (Hi_pos : 0 < i).
  {
    match goal with
    | Hprev : in_word = 1 -> 0 < i /\ Znth (i - 1) l 0 <> 32 |- _ =>
        destruct (Hprev Hin_word_one) as [Hpos _]; exact Hpos
    end.
  }
  assert (Hprefix_next :
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l 0 :: nil).
  {
    apply sublist_prefix_snoc_Z.
    lia.
  }
  assert (Hprefix_cur :
    sublist 0 i l = sublist 0 (i - 1) l ++ Znth (i - 1) l 0 :: nil).
  {
    replace i with ((i - 1) + 1) at 1 by lia.
    apply sublist_prefix_snoc_Z.
    lia.
  }
  rewrite Hprefix_next.
  rewrite Hprefix_cur.
  rewrite Hprefix_cur in H9.
  rewrite string_count_words_simple_spec_app_nonspace_nonspace
    by assumption.
  assert (Hnext_in_word :
    in_word = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) l 0 <> 32).
  {
    intros _.
    split.
    - lia.
    - replace (i + 1 - 1) with i by lia.
      exact Hcur_nonspace.
  }
  entailer!; try lia.
Qed.

Lemma proof_of_string_count_words_simple_entail_wit_3 : string_count_words_simple_entail_wit_3.
Proof.
  unfold string_count_words_simple_entail_wit_3.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Hnz : Znth i l 0 <> 0).
      {
        match goal with
        | Hforall : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hforall; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  rewrite sublist_self in H7 by lia.
  entailer!.
Qed.
