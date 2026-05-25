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
From SimpleC.EE.CAV.verify_20260423_033114_string_replace_char Require Import string_replace_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma current_head_after_prefix :
  forall (pre xs : list Z) (x i d : Z),
    Zlength pre = i ->
    Znth i (pre ++ x :: xs) d = x.
Proof.
  intros pre xs x i d Hlen.
  rewrite app_Znth2 by lia.
  replace (i - Zlength pre) with 0 by lia.
  simpl. reflexivity.
Qed.

Lemma replace_at_prefix_end :
  forall (pre tail : list Z) (old i x : Z),
    Zlength pre = i ->
    replace_Znth i x (pre ++ old :: tail) =
    pre ++ x :: tail.
Proof.
  intros pre tail old i x Hlen.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (i - Zlength pre) with 0 by lia.
  unfold replace_Znth.
  replace (Z.to_nat 0) with 0%nat by lia.
  simpl. reflexivity.
Qed.

Lemma Znth_cons_succ :
  forall (xs : list Z) (x k d : Z),
    0 <= k ->
    Znth (1 + k) (x :: xs) d = Znth k xs d.
Proof.
  intros xs x k d Hk.
  rewrite Znth_cons by lia.
  replace (1 + k - 1) with k by lia.
  reflexivity.
Qed.

Lemma proof_of_string_replace_char_entail_wit_1 : string_replace_char_entail_wit_1.
Proof.
  pre_process.
  Exists (l ++ 0 :: nil) (@nil Z).
  entailer!.
  - replace (n - 0) with (Zlength l) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    simpl. reflexivity.
  - intros t Ht.
    replace (0 + t) with t by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_string_replace_char_entail_wit_2_1 : string_replace_char_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - 
    assert (Hi_eq : i = n) by lia.
    subst i.
    rewrite app_Znth2 in H1 by lia.
    replace (Zlength l1_2 - Zlength l1_2) with 0 in H1 by lia.
    replace (n - Zlength l1_2) with 0 in H10 by lia.
    replace (Znth 0 l2_2 0) with 0 in H1 by (symmetry; exact H10).
    contradiction.
  }
  destruct l2_2.
  - match goal with
    | Hlen2 : Zlength nil = (n + 1 - i) |- _ =>
        rewrite Zlength_nil in Hlen2; lia
    end.
  - rename z into x. rename l2_2 into xs.
    assert (Hcur_x : Znth i (l1_2 ++ x :: xs) 0 = x).
    {
      match goal with
      | Hlen1 : Zlength l1_2 = i |- _ =>
          apply current_head_after_prefix; exact Hlen1
      end.
    }
    rewrite Hcur_x in *.
    rewrite replace_at_prefix_end.
    2: match goal with Hlen1 : Zlength l1_2 = i |- _ => exact Hlen1 end.
    Exists xs (l1_2 ++ new_c_pre :: nil).
    entailer!.
    + rewrite <- app_assoc. simpl. entailer!.
    + replace (n - (i + 1)) with (n - i - 1) by lia.
      replace (n - i) with (1 + (n - i - 1)) in H10 by lia.
      rewrite Znth_cons_succ in H10 by lia.
      exact H10.
    + intros t Ht.
      specialize (H9 (1 + t) ltac:(lia)).
      rewrite Znth_cons_succ in H9 by lia.
      replace (i + (1 + t)) with (i + 1 + t) in H9 by lia.
      exact H9.
    + intros t Ht.
      destruct (Z.eq_dec t i) as [Ht_eq | Ht_ne].
      * subst t.
        rewrite app_Znth2 by lia.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl. assumption.
      * rewrite app_Znth1 by lia.
        match goal with
        | Hnz : forall t : Z, _ -> Znth t l1_2 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
    + intros t Ht.
      destruct (Z.eq_dec t i) as [Ht_eq | Ht_ne].
      * subst t.
        rewrite app_Znth2 by lia.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl.
        split.
        -- intros _. reflexivity.
        -- intros Hneq.
           exfalso. apply Hneq.
           specialize (H9 0 ltac:(lia)).
           simpl in H9.
           replace (i + 0) with i in H9 by lia.
           rewrite <- H9.
           exact H0.
      * assert (Ht_lt_i : t < i) by lia.
        rewrite app_Znth1 by lia.
        apply H7; lia.
    + match goal with
      | Hlen2 : Zlength (x :: xs) = (n + 1 - i) |- _ =>
          rewrite Zlength_cons in Hlen2; lia
      end.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_string_replace_char_entail_wit_2_2 : string_replace_char_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    -
    assert (Hi_eq : i = n) by lia.
    subst i.
    rewrite app_Znth2 in H0 by lia.
    replace (Zlength l1_2 - Zlength l1_2) with 0 in H0 by lia.
    replace (n - Zlength l1_2) with 0 in H9 by lia.
    replace (Znth 0 l2_2 0) with 0 in H0 by (symmetry; exact H9).
    contradiction.
  }
  destruct l2_2.
  - match goal with
    | Hlen2 : Zlength nil = (n + 1 - i) |- _ =>
        rewrite Zlength_nil in Hlen2; lia
    end.
  - rename z into x. rename l2_2 into xs.
    assert (Hcur_x : Znth i (l1_2 ++ x :: xs) 0 = x).
    {
      match goal with
      | Hlen1 : Zlength l1_2 = i |- _ =>
          apply current_head_after_prefix; exact Hlen1
      end.
    }
    rewrite Hcur_x in *.
    Exists xs (l1_2 ++ x :: nil).
    entailer!.
    + rewrite <- app_assoc. simpl. entailer!.
    + replace (n - (i + 1)) with (n - i - 1) by lia.
      replace (n - i) with (1 + (n - i - 1)) in H9 by lia.
      rewrite Znth_cons_succ in H9 by lia.
      exact H9.
    + intros t Ht.
      specialize (H8 (1 + t) ltac:(lia)).
      rewrite Znth_cons_succ in H8 by lia.
      replace (i + (1 + t)) with (i + 1 + t) in H8 by lia.
      exact H8.
    + intros t Ht.
      destruct (Z.eq_dec t i) as [Ht_eq | Ht_ne].
      * subst t.
        rewrite app_Znth2 by lia.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl.
        specialize (H8 0 ltac:(lia)).
        rewrite Znth0_cons in H8.
        replace (i + 0) with i in H8 by lia.
        rewrite H8.
        apply H14; lia.
      * rewrite app_Znth1 by lia.
        apply H7; lia.
    + intros t Ht.
      destruct (Z.eq_dec t i) as [Ht_eq | Ht_ne].
      * subst t.
        rewrite app_Znth2 by lia.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl.
        split.
        -- intros Hold.
           exfalso. apply H.
           specialize (H8 0 ltac:(lia)).
           rewrite Znth0_cons in H8.
           replace (i + 0) with i in H8 by lia.
           rewrite H8. exact Hold.
        -- intros _.
           specialize (H8 0 ltac:(lia)).
           rewrite Znth0_cons in H8.
           replace (i + 0) with i in H8 by lia.
           exact H8.
      * assert (Ht_lt_i : t < i) by lia.
        rewrite app_Znth1 by lia.
        apply H6; lia.
    + match goal with
      | Hlen2 : Zlength (x :: xs) = (n + 1 - i) |- _ =>
          rewrite Zlength_cons in Hlen2; lia
      end.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_string_replace_char_return_wit_1 : string_replace_char_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq_n : i_2 = n).
  {
    destruct (Z_lt_ge_dec i_2 n) as [Hlt | Hge].
    - rewrite app_Znth2 in H by lia.
      replace (i_2 - Zlength l1) with 0 in H by lia.
      specialize (H7 0 ltac:(lia)).
      replace (i_2 + 0) with i_2 in H7 by lia.
      rewrite H7 in H.
      specialize (H13 i_2 ltac:(lia)).
      contradiction.
    - lia.
  }
  subst i_2.
  assert (Hl2_single : l2 = 0 :: nil).
  {
    destruct l2.
    - rewrite Zlength_nil in *. lia.
    - rename z into x. rename l2 into xs.
      assert (Hx0 : x = 0).
      {
        replace (n - Zlength l1) with 0 in H8 by lia.
        rewrite Znth0_cons in H8.
        exact H8.
      }
      subst x.
      destruct xs.
      + reflexivity.
      + rename z into y. rename xs into ys.
        repeat rewrite Zlength_cons in *.
        pose proof (Zlength_nonneg ys).
        lia.
  }
  subst l2.
  Exists l1.
  entailer!.
  - intros k Hk.
    apply H6. lia.
  - intros i Hi.
    apply H5. lia.
Qed. 
