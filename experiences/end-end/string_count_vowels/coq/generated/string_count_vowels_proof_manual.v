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
From SimpleC.EE.CAV.verify_20260423_012416_string_count_vowels Require Import string_count_vowels_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_vowels.
Local Open Scope sac.

Lemma string_count_vowels_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_vowels_spec (l ++ x :: nil) =
    string_count_vowels_spec l +
    (if Z.eq_dec x 97 then 1
     else if Z.eq_dec x 101 then 1
     else if Z.eq_dec x 105 then 1
     else if Z.eq_dec x 111 then 1
     else if Z.eq_dec x 117 then 1
     else 0).
Proof.
  induction l; intros x.
  - simpl.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  - simpl.
    destruct (Z.eq_dec a 97);
      destruct (Z.eq_dec a 101);
      destruct (Z.eq_dec a 105);
      destruct (Z.eq_dec a 111);
      destruct (Z.eq_dec a 117);
      rewrite IHl;
      destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
Qed.

Ltac prepare_vowel_step :=
  pre_process;
  match goal with
  | Hnz : Znth ?ii (?ll ++ 0 :: nil) 0 <> 0,
    Hlen : Zlength ?ll = ?nn |- _ =>
      assert (Hlen_l : Zlength ll = nn)
        by exact Hlen
  end;
  match goal with
  | Hnz : Znth ?ii (?ll ++ 0 :: nil) 0 <> 0,
    Hle : ?ii <= ?nn,
    Hlen_l : Zlength ?ll = ?nn |- _ =>
      assert (Hi_lt_n : ii < nn)
        by (destruct (Z_lt_ge_dec ii nn) as [Hlt | Hge];
            [ exact Hlt
            | assert (Hi_eq : ii = nn) by lia;
              rewrite Hi_eq in Hnz;
              rewrite app_Znth2 in Hnz by lia;
              replace (nn - Zlength ll) with 0 in Hnz by lia;
              simpl in Hnz;
              exfalso; apply Hnz; reflexivity ])
  end;
  match goal with
  | Heq : ?ll = ?l1 ++ ?l2 |- _ => subst ll
  end;
  match goal with
  | l2_2 : list Z |- _ => destruct l2_2
  end;
  [ exfalso; repeat rewrite app_nil_r in *; lia
  | rename z into x;
    rename l2_2 into xs ].

Ltac expose_current_char H :=
  match goal with
  | i : Z, l1_2 : list Z, x : Z, xs : list Z |- _ =>
      rewrite <- app_assoc in H;
      rewrite app_Znth2 in H by lia;
      replace (i - Zlength l1_2) with 0 in H by lia;
      simpl in H;
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H
  end.

Ltac finish_vowel_step :=
  match goal with
  | i : Z, l1_2 : list Z, x : Z, xs : list Z |- _ =>
      assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
        by (rewrite <- app_assoc; reflexivity);
      assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
        by (rewrite Zlength_app_cons; lia);
      Exists (l1_2 ++ x :: nil);
      Exists xs;
      entailer!
  end.

Lemma proof_of_string_count_vowels_entail_wit_1 : string_count_vowels_entail_wit_1.
Proof.
  unfold string_count_vowels_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_1 : string_count_vowels_entail_wit_2_1.
Proof.
  unfold string_count_vowels_entail_wit_2_1.
  prepare_vowel_step.
  assert (Hx_eq : x = 117)
    by (match goal with
        | H : ?t = 117 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            lia
        end).
  assert (Hspec_next :
    cnt + 1 = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_2 : string_count_vowels_entail_wit_2_2.
Proof.
  unfold string_count_vowels_entail_wit_2_2.
  prepare_vowel_step.
  assert (Hx_eq : x = 105)
    by (match goal with
        | H : ?t = 105 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            lia
        end).
  assert (Hspec_next :
    cnt + 1 = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_3 : string_count_vowels_entail_wit_2_3.
Proof.
  unfold string_count_vowels_entail_wit_2_3.
  prepare_vowel_step.
  assert (Hx_eq : x = 97)
    by (match goal with
        | H : ?t = 97 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            lia
        end).
  assert (Hspec_next :
    cnt + 1 = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_4 : string_count_vowels_entail_wit_2_4.
Proof.
  unfold string_count_vowels_entail_wit_2_4.
  prepare_vowel_step.
  assert (Hx_eq : x = 101)
    by (match goal with
        | H : ?t = 101 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            lia
        end).
  assert (Hspec_next :
    cnt + 1 = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_5 : string_count_vowels_entail_wit_2_5.
Proof.
  unfold string_count_vowels_entail_wit_2_5.
  prepare_vowel_step.
  assert (Hx_eq : x = 111)
    by (match goal with
        | H : ?t = 111 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            lia
        end).
  assert (Hspec_next :
    cnt + 1 = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_2_6 : string_count_vowels_entail_wit_2_6.
Proof.
  unfold string_count_vowels_entail_wit_2_6.
  prepare_vowel_step.
  assert (Hx_ne_97 : x <> 97)
    by (match goal with
        | H : ?t <> 97 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            exact H
        end).
  assert (Hx_ne_101 : x <> 101)
    by (match goal with
        | H : ?t <> 101 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            exact H
        end).
  assert (Hx_ne_105 : x <> 105)
    by (match goal with
        | H : ?t <> 105 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            exact H
        end).
  assert (Hx_ne_111 : x <> 111)
    by (match goal with
        | H : ?t <> 111 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            exact H
        end).
  assert (Hx_ne_117 : x <> 117)
    by (match goal with
        | H : ?t <> 117 |- _ =>
            rewrite <- app_assoc in H;
            rewrite app_Znth2 in H by lia;
            replace (i - Zlength l1_2) with 0 in H by lia;
            simpl in H;
            change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H;
            exact H
        end).
  assert (Hspec_next :
    cnt = string_count_vowels_spec (l1_2 ++ x :: nil)).
  {
    subst cnt.
    rewrite string_count_vowels_spec_app_single.
    destruct (Z.eq_dec x 97);
      destruct (Z.eq_dec x 101);
      destruct (Z.eq_dec x 105);
      destruct (Z.eq_dec x 111);
      destruct (Z.eq_dec x 117);
      lia.
  }
  assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs)
    by (rewrite <- app_assoc; reflexivity).
  assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1)
    by (rewrite Zlength_app_cons; lia).
  Exists (l1_2 ++ x :: nil).
  Exists xs.
  entailer!.
Qed.

Lemma proof_of_string_count_vowels_entail_wit_3 : string_count_vowels_entail_wit_3.
Proof.
  unfold string_count_vowels_entail_wit_3.
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
      match goal with
      | Hzero : Znth i (l ++ 0 :: nil) 0 = 0 |- _ =>
          rewrite app_Znth1 in Hzero by lia;
          contradiction
      end.
    - lia.
  }
  subst i.
  assert (Hl1_eq_l : l1_2 = l).
  {
    subst l.
    destruct l2_2.
    - rewrite app_nil_r.
      reflexivity.
    - rename z into x.
      rename l2_2 into xs.
      exfalso.
      rewrite Zlength_app, Zlength_cons in Hlen_l.
      pose proof Zlength_nonneg xs.
      lia.
  }
  assert (Hspec_full : cnt = string_count_vowels_spec l).
  {
    subst cnt.
    rewrite Hl1_eq_l.
    reflexivity.
  }
  replace (Zlength l1_2) with n by lia.
  Exists l.
  Exists nil.
  entailer!; try rewrite app_nil_r; try reflexivity.
Qed.
