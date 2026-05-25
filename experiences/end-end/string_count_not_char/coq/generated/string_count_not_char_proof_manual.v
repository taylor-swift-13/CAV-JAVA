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
From SimpleC.EE.CAV.verify_20260423_005835_string_count_not_char Require Import string_count_not_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_not_char.
Local Open Scope sac.

Lemma string_count_not_char_spec_app :
  forall (a b : list Z) (c : Z),
    string_count_not_char_spec (a ++ b) c =
    string_count_not_char_spec a c + string_count_not_char_spec b c.
Proof.
  induction a; intros b c.
  - simpl. lia.
  - simpl.
    destruct (Z.eq_dec a c); rewrite IHa; lia.
Qed.

Lemma string_count_not_char_spec_app_single_neq :
  forall (l : list Z) (x c : Z),
    x <> c ->
    string_count_not_char_spec (l ++ x :: nil) c =
    string_count_not_char_spec l c + 1.
Proof.
  intros l x c Hneq.
  rewrite string_count_not_char_spec_app.
  simpl.
  destruct (Z.eq_dec x c); lia.
Qed.

Lemma string_count_not_char_spec_app_single_eq :
  forall (l : list Z) (x c : Z),
    x = c ->
    string_count_not_char_spec (l ++ x :: nil) c =
    string_count_not_char_spec l c.
Proof.
  intros l x c Heq.
  rewrite string_count_not_char_spec_app.
  simpl.
  destruct (Z.eq_dec x c); lia.
Qed.

Lemma proof_of_string_count_not_char_entail_wit_1 : string_count_not_char_entail_wit_1.
Proof.
  unfold string_count_not_char_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_count_not_char_entail_wit_2_1 : string_count_not_char_entail_wit_2_1.
Proof.
  unfold string_count_not_char_entail_wit_2_1.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H0 by lia.
      replace (Zlength l1_2 - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + assert (Hxneq : x <> c_pre).
      {
        rewrite <- app_assoc in H.
        rewrite app_Znth2 in H by lia.
        replace (i - Zlength l1_2) with 0 in H by lia.
        simpl in H.
        exact H.
      }
      rewrite string_count_not_char_spec_app_single_neq by exact Hxneq.
      lia.
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_string_count_not_char_entail_wit_2_2 : string_count_not_char_entail_wit_2_2.
Proof.
  unfold string_count_not_char_entail_wit_2_2.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H0 by lia.
      replace (Zlength l1_2 - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + assert (Hx : x = c_pre).
      {
        rewrite <- app_assoc in H.
        rewrite app_Znth2 in H by lia.
        replace (i - Zlength l1_2) with 0 in H by lia.
        simpl in H.
        exact H.
      }
      rewrite string_count_not_char_spec_app_single_eq by exact Hx.
      lia.
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_string_count_not_char_return_wit_1 : string_count_not_char_return_wit_1.
Proof.
  unfold string_count_not_char_return_wit_1.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Znth i l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  entailer!.
  destruct l2.
  - match goal with
    | Hshape : l = l1 ++ nil |- _ => rewrite Hshape
    end.
    rewrite app_nil_r.
    match goal with
    | Hcount : count = string_count_not_char_spec l1 c_pre |- _ =>
        exact Hcount
    end.
  - rename z into x.
    rename l2 into xs.
    exfalso.
    match goal with
    | Hshape : l = l1 ++ x :: xs |- _ => rewrite Hshape in *
    end.
    match goal with
    | Hlen : Zlength (l1 ++ x :: xs) = n |- _ =>
        rewrite Zlength_app, Zlength_cons in Hlen
    end.
    pose proof Zlength_nonneg xs.
    lia.
Qed.
