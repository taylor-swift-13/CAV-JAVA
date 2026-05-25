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
From SimpleC.EE.CAV.verify_20260423_032238_string_remove_char_to_output Require Import string_remove_char_to_output_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_remove_char_to_output.
Local Open Scope sac.

Lemma string_remove_char_to_output_spec_app :
  forall a b c,
    string_remove_char_to_output_spec (a ++ b) c =
    string_remove_char_to_output_spec a c ++
    string_remove_char_to_output_spec b c.
Proof.
  induction a; intros b c; simpl; auto.
  destruct (Z.eq_dec a c); rewrite IHa; auto.
Qed.

Lemma string_remove_char_to_output_spec_keep_single :
  forall l x c,
    x <> c ->
    string_remove_char_to_output_spec (l ++ x :: nil) c =
    string_remove_char_to_output_spec l c ++ x :: nil.
Proof.
  intros l x c Hx.
  rewrite string_remove_char_to_output_spec_app.
  simpl.
  destruct (Z.eq_dec x c); [lia | reflexivity].
Qed.

Lemma string_remove_char_to_output_spec_drop_single :
  forall l x c,
    x = c ->
    string_remove_char_to_output_spec (l ++ x :: nil) c =
    string_remove_char_to_output_spec l c.
Proof.
  intros l x c Hx.
  rewrite string_remove_char_to_output_spec_app.
  simpl.
  destruct (Z.eq_dec x c); [rewrite app_nil_r; reflexivity | lia].
Qed.

Lemma string_remove_char_to_output_spec_zlength_le :
  forall l c,
    0 <= Zlength (string_remove_char_to_output_spec l c) <= Zlength l.
Proof.
  induction l; intros c.
  - simpl. rewrite Zlength_nil. lia.
  - simpl.
    destruct (Z.eq_dec a c).
    + repeat rewrite Zlength_cons. specialize (IHl c). lia.
    + repeat rewrite Zlength_cons. specialize (IHl c). lia.
Qed.

Lemma current_head_after_prefix :
  forall (l1 xs : list Z) (x i : Z),
    Zlength l1 = i ->
    Znth i ((l1 ++ x :: xs) ++ 0 :: nil) 0 = x.
Proof.
  intros l1 x xs i Hlen.
  rewrite <- app_assoc.
  rewrite app_Znth2 by lia.
  replace (i - Zlength l1) with 0 by lia.
  simpl. reflexivity.
Qed.

Lemma replace_at_prefix_end :
  forall (pre tail : list Z) (old j x : Z),
    Zlength pre = j ->
    replace_Znth j x (pre ++ old :: tail) =
    pre ++ x :: tail.
Proof.
  intros pre old tail j x Hlen.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (j - Zlength pre) with 0 by lia.
  unfold replace_Znth.
  replace (Z.to_nat 0) with 0%nat by lia.
  simpl. reflexivity.
Qed.

Lemma proof_of_string_remove_char_to_output_entail_wit_1 : string_remove_char_to_output_entail_wit_1.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full s_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full out_pre (n + 1) d)).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full out_pre (n + 1) d)
             (CharArray.full s_pre (n + 1) (l ++ 0 :: nil))).
  Exists d (@nil Z) l.
  entailer!.
  rewrite Zlength_correct. lia.
Qed. 

Lemma proof_of_string_remove_char_to_output_entail_wit_2_1 : string_remove_char_to_output_entail_wit_2_1.
Proof.
  pre_process.
  pose proof (string_remove_char_to_output_spec_zlength_le l1_2 c_pre) as Hspec_len.
  assert (Hi_lt_n : Zlength l1_2 < n).
  {
    destruct (Z_lt_ge_dec (Zlength l1_2) n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Zlength l1_2 = n) by lia.
      rewrite app_Znth2 in H0 by lia.
      replace (i - Zlength l) with 0 in H0 by lia.
      simpl in H0. contradiction H0. reflexivity.
  }
  subst l.
  destruct l2_2 eqn:Hl2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0. contradiction H0. reflexivity.
  - rename z into x. rename l into xs.
    destruct d1_2 eqn:Hd1.
    + rewrite Zlength_nil in H9. lia.
    + rename z into old. rename l into tail.
      assert (Hcur : Znth i ((l1_2 ++ x :: xs) ++ 0 :: nil) 0 = x)
        by (apply current_head_after_prefix; exact H7).
      rewrite Hcur in *.
      assert (Hrep :
        replace_Znth j x (string_remove_char_to_output_spec l1_2 c_pre ++ old :: tail) =
        string_remove_char_to_output_spec l1_2 c_pre ++ x :: tail).
      {
        apply replace_at_prefix_end.
        lia.
      }
      rewrite Hrep.
      rewrite (logic_equiv_sepcon_comm
                 (CharArray.full out_pre (n + 1)
                    (string_remove_char_to_output_spec l1_2 c_pre ++ x :: tail))
                 (CharArray.full s_pre (n + 1) ((l1_2 ++ x :: xs) ++ 0 :: nil))).
      Exists tail (l1_2 ++ x :: nil) xs.
      entailer!;
        try (rewrite string_remove_char_to_output_spec_keep_single by exact H);
        try rewrite Zlength_app_cons;
        try (rewrite Zlength_cons in H9);
        try rewrite <- app_assoc;
        simpl;
        try lia;
        try reflexivity.
Qed. 

Lemma proof_of_string_remove_char_to_output_entail_wit_2_2 : string_remove_char_to_output_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_lt_n : Zlength l1_2 < n).
  {
    destruct (Z_lt_ge_dec (Zlength l1_2) n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Zlength l1_2 = n) by lia.
      rewrite app_Znth2 in H0 by lia.
      replace (i - Zlength l) with 0 in H0 by lia.
      simpl in H0. contradiction H0. reflexivity.
  }
  subst l.
  destruct l2_2 eqn:Hl2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0. contradiction H0. reflexivity.
  - rename z into x. rename l into xs.
    assert (Hcur : Znth i ((l1_2 ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H7).
    rewrite Hcur in *.
    Exists d1_2 (l1_2 ++ x :: nil) xs.
    entailer!;
      try (rewrite string_remove_char_to_output_spec_drop_single by exact H);
      try rewrite Zlength_app_cons;
      try rewrite <- app_assoc;
      simpl;
      try lia;
      try reflexivity.
  all: try (rewrite Zlength_nil in H8; lia);
       try (rewrite Zlength_cons in H8; lia);
       try rewrite <- app_assoc;
       simpl;
       try lia;
       try reflexivity.
  Unshelve.
  all: try exact (@nil Z); try exact 0; try lia; try reflexivity.
Qed. 

Lemma proof_of_string_remove_char_to_output_entail_wit_3 : string_remove_char_to_output_entail_wit_3.
Proof.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - specialize (H9 i).
      assert (Znth i l 0 <> 0) by (apply H9; lia).
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  assert (Hl2_nil : l2 = nil).
  {
    destruct l2.
    - reflexivity.
    - exfalso.
      rewrite H5 in H12.
      rewrite Zlength_app in H12.
      rewrite Hi_eq_n in H12.
      rewrite Zlength_cons in H12.
      pose proof (Zlength_nonneg l2).
      lia.
  }
  subst l2.
  rewrite app_nil_r in H5.
  subst l.
  rewrite Hi_eq_n.
  destruct d1.
  - rewrite Zlength_nil in H8. lia.
  - rename z into x. rename d1 into t.
    assert (Hout_shape :
      string_remove_char_to_output_spec l1 c_pre ++ x :: t =
      (string_remove_char_to_output_spec l1 c_pre ++ x :: nil) ++ t).
    {
      rewrite <- app_assoc.
      reflexivity.
    }
    rewrite Hout_shape.
    Exists x t.
    entailer!;
      try (rewrite Zlength_cons in H8; lia);
      try rewrite <- app_assoc;
      simpl;
      try lia;
      try reflexivity.
Qed. 

Lemma proof_of_string_remove_char_to_output_return_wit_1 : string_remove_char_to_output_return_wit_1.
Proof.
  pre_process.
  Exists t_2.
  assert (Hrep :
    replace_Znth j 0
      ((string_remove_char_to_output_spec l c_pre ++ x :: nil) ++ t_2) =
    (string_remove_char_to_output_spec l c_pre ++ 0 :: nil) ++ t_2).
  {
    rewrite <- app_assoc.
    simpl.
    rewrite replace_at_prefix_end by lia.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hrep.
  entailer!.
Qed. 
