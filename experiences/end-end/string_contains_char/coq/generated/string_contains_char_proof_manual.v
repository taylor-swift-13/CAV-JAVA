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
From SimpleC.EE.CAV.verify_20260422_234921_string_contains_char Require Import string_contains_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_contains_char.
Local Open Scope sac.

Lemma string_contains_char_spec_app_single :
  forall (l : list Z) (x c : Z),
    string_contains_char_spec l c = 0 ->
    string_contains_char_spec (l ++ x :: nil) c =
    if Z.eq_dec x c then 1 else 0.
Proof.
  induction l; intros x c Hspec.
  - simpl. destruct (Z.eq_dec x c); reflexivity.
  - simpl in Hspec.
    destruct (Z.eq_dec a c) as [Heq | Hneq].
    + discriminate.
    + simpl. destruct (Z.eq_dec a c); try contradiction.
      apply IHl.
      exact Hspec.
Qed.

Lemma string_contains_char_spec_app_hit :
  forall (l1 l2 : list Z) (x c : Z),
    string_contains_char_spec l1 c = 0 ->
    x = c ->
    string_contains_char_spec (l1 ++ x :: l2) c = 1.
Proof.
  induction l1; intros l2 x c Hspec Hx.
  - simpl. subst x. destruct (Z.eq_dec c c); [reflexivity | contradiction].
  - simpl in Hspec.
    destruct (Z.eq_dec a c) as [Heq | Hneq].
    + discriminate.
    + simpl. destruct (Z.eq_dec a c); try contradiction.
      apply IHl1 with (x := x).
      * exact Hspec.
      * exact Hx.
Qed.

Lemma proof_of_string_contains_char_entail_wit_1 : string_contains_char_entail_wit_1.
Proof.
  unfold string_contains_char_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_contains_char_entail_wit_2 : string_contains_char_entail_wit_2.
Proof.
  unfold string_contains_char_entail_wit_2.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      match goal with
      | Hpref : Zlength l1_2 = n |- _ =>
          rewrite app_Znth2 in H0 by lia;
          replace (Zlength l1_2 - Zlength l) with 0 in H0 by (rewrite Hpref, Hlen_l; lia);
          simpl in H0;
          exfalso;
          apply H0;
          reflexivity
      end.
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
      rewrite string_contains_char_spec_app_single by exact H5.
      destruct (Z.eq_dec x c_pre); [contradiction | reflexivity].
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_string_contains_char_return_wit_1 : string_contains_char_return_wit_1.
Proof.
  unfold string_contains_char_return_wit_1.
  intros.
  entailer!.
  subst l.
  destruct l2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1) with 0 in H0 by lia.
    simpl in H0.
    contradiction.
  - rename z into x.
    rename l2 into xs.
    assert (Hx : x = c_pre).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1) with 0 in H by lia.
      simpl in H.
      exact H.
    }
    subst x.
    symmetry.
    apply string_contains_char_spec_app_hit with (l1 := l1) (l2 := xs).
    + exact H5.
    + reflexivity.
Qed.

Lemma proof_of_string_contains_char_return_wit_2 : string_contains_char_return_wit_2.
Proof.
  unfold string_contains_char_return_wit_2.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
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
  - rewrite H2.
    rewrite app_nil_r.
    symmetry.
    exact H4.
  - rename z into x.
    rename l2 into xs.
    exfalso.
    rewrite H2 in Hlen_l.
    rewrite Zlength_app, Zlength_cons in Hlen_l.
    pose proof Zlength_nonneg xs.
    lia.
Qed.
