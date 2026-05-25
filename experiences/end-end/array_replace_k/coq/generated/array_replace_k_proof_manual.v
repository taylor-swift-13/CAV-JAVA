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
From SimpleC.EE.CAV.verify_20260422_072722_array_replace_k Require Import array_replace_k_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma list_eq_by_Znth :
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    (forall k, 0 <= k < Zlength l1 -> Znth k l1 0 = Znth k l2 0) ->
    l1 = l2.
Proof.
  intros l1.
  induction l1.
  - intros l2 Hlen _.
    rewrite Zlength_nil in Hlen.
    symmetry in Hlen.
    apply Zlength_nil_inv in Hlen.
    subst l2.
    reflexivity.
  - intros l2 Hlen Hnth.
    destruct l2.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg l1).
      lia.
    + f_equal.
      * assert (0 <= 0 < Zlength (a :: l1)).
        {
          rewrite Zlength_cons.
          pose proof (Zlength_nonneg l1).
          lia.
        }
        specialize (Hnth 0 H).
        simpl in Hnth.
        exact Hnth.
      * apply IHl1.
        -- rewrite !Zlength_cons in Hlen.
           lia.
        -- intros k Hk.
           assert (0 <= k + 1 < Zlength (a :: l1)).
           {
             rewrite Zlength_cons.
             pose proof (Zlength_nonneg l1).
             lia.
           }
           specialize (Hnth (k + 1) H).
           rewrite !Znth_cons in Hnth by lia.
           replace (k + 1 - 1) with k in Hnth by lia.
           exact Hnth.
Qed.

Lemma proof_of_array_replace_k_entail_wit_1 : array_replace_k_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  Exists (@nil Z).
  rewrite app_nil_l.
  entailer!.
Qed. 

Lemma proof_of_array_replace_k_entail_wit_2_1 : array_replace_k_entail_wit_2_1.
Proof.
  pre_process.
  Exists (sublist (i + 1) n_pre l).
  Exists (app l1_2 (new_k_pre :: nil)).
  assert (Hl2 : l2_2 = sublist i n_pre l).
  {
    apply list_eq_by_Znth.
    - match goal with
      | Hlen2 : Zlength l2_2 = n_pre - i |- _ => rewrite Hlen2
      end.
      rewrite Zlength_sublist by lia.
      lia.
    - intros k Hk.
      rewrite Znth_sublist; try lia.
      match goal with
      | Hsuffix : forall k_2 : Z,
          ((0 <= k_2) /\ (k_2 < (n_pre - i))) ->
          Znth k_2 l2_2 0 = Znth (i + k_2) l 0 |- _ =>
          rewrite Hsuffix by lia
      end.
      replace (k + i) with (i + k) by lia.
      replace (i + (k - i)) with k by lia.
      reflexivity.
  }
  assert (Hli_eq : Znth i l 0 = old_k_pre).
  {
    match goal with
    | Hcur : Znth i (l1_2 ++ l2_2) 0 = old_k_pre |- _ =>
        rewrite app_Znth2 in Hcur by lia;
        replace (i - Zlength l1_2) with 0 in Hcur by lia;
        match goal with
        | Hsuffix : forall k_2 : Z,
            ((0 <= k_2) /\ (k_2 < (n_pre - i))) ->
            Znth k_2 l2_2 0 = Znth (i + k_2) l 0 |- _ =>
            rewrite Hsuffix in Hcur by lia
        end;
        replace (i + 0) with i in Hcur by lia;
        exact Hcur
    end.
  }
  assert (Hreplace :
    replace_Znth i new_k_pre (app l1_2 l2_2) =
    app (app l1_2 (new_k_pre :: nil)) (sublist (i + 1) n_pre l)).
  {
    rewrite Hl2.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i - Zlength l1_2) with 0 by lia.
    rewrite (sublist_split i n_pre (i + 1) l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
    unfold replace_Znth.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hreplace.
  entailer!.
  - intros k Hk.
    rewrite Znth_sublist; try lia;
    replace (k + (i + 1)) with (i + 1 + k) by lia;
    reflexivity.
  - intros k Hk.
    destruct Hk as [Hk0 Hklt].
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1.
      * try rewrite app_Znth1 by lia.
        match goal with
        | Hprefix : forall t : Z,
            ((0 <= t) /\ (t < i)) ->
            ((Znth t l 0 = old_k_pre -> Znth t l1_2 0 = new_k_pre) /\
             (Znth t l 0 <> old_k_pre -> Znth t l1_2 0 = Znth t l 0)) |- _ =>
            exact (Hprefix k ltac:(lia))
        end.
      * try rewrite Zlength_app; simpl; lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2.
      * try rewrite Zlength_app.
        simpl.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl.
        split.
        -- intros _; reflexivity.
        -- intros Hneq; lia.
      * try rewrite Zlength_app; simpl; lia.
  - rewrite Zlength_sublist by lia. lia.
  - try rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed. 

Lemma proof_of_array_replace_k_entail_wit_2_2 : array_replace_k_entail_wit_2_2.
Proof.
  pre_process.
  Exists (sublist (i + 1) n_pre l).
  Exists (app l1_2 (Znth i l 0 :: nil)).
  assert (Hl2 : l2_2 = sublist i n_pre l).
  {
    apply list_eq_by_Znth.
    - match goal with
      | Hlen2 : Zlength l2_2 = n_pre - i |- _ => rewrite Hlen2
      end.
      rewrite Zlength_sublist by lia.
      lia.
    - intros k Hk.
      rewrite Znth_sublist; try lia.
      match goal with
      | Hsuffix : forall k_2 : Z,
          ((0 <= k_2) /\ (k_2 < (n_pre - i))) ->
          Znth k_2 l2_2 0 = Znth (i + k_2) l 0 |- _ =>
          rewrite Hsuffix by lia
      end.
      replace (k + i) with (i + k) by lia.
      replace (i + (k - i)) with k by lia.
      reflexivity.
  }
  assert (Hli_neq : Znth i l 0 <> old_k_pre).
  {
    match goal with
    | Hcur : Znth i (l1_2 ++ l2_2) 0 <> old_k_pre |- _ =>
        rewrite app_Znth2 in Hcur by lia;
        replace (i - Zlength l1_2) with 0 in Hcur by lia;
        match goal with
        | Hsuffix : forall k_2 : Z,
            ((0 <= k_2) /\ (k_2 < (n_pre - i))) ->
            Znth k_2 l2_2 0 = Znth (i + k_2) l 0 |- _ =>
            rewrite Hsuffix in Hcur by lia
        end;
        replace (i + 0) with i in Hcur by lia;
        exact Hcur
    end.
  }
  assert (Happ :
    app l1_2 l2_2 =
    app (app l1_2 (Znth i l 0 :: nil)) (sublist (i + 1) n_pre l)).
  {
    rewrite Hl2.
    rewrite (sublist_split i n_pre (i + 1) l) by (pose proof (Zlength_correct l); lia).
    rewrite (sublist_single i l 0) by (pose proof (Zlength_correct l); lia).
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Happ.
  entailer!.
  - intros k Hk.
    rewrite Znth_sublist; try lia;
    replace (k + (i + 1)) with (i + 1 + k) by lia;
    reflexivity.
  - intros k Hk.
    destruct Hk as [Hk0 Hklt].
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1.
      * try rewrite app_Znth1 by lia.
        match goal with
        | Hprefix : forall t : Z,
            ((0 <= t) /\ (t < i)) ->
            ((Znth t l 0 = old_k_pre -> Znth t l1_2 0 = new_k_pre) /\
             (Znth t l 0 <> old_k_pre -> Znth t l1_2 0 = Znth t l 0)) |- _ =>
            exact (Hprefix k ltac:(lia))
        end.
      * try rewrite Zlength_app; simpl; lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2.
      * try rewrite Zlength_app.
        simpl.
        replace (i - Zlength l1_2) with 0 by lia.
        simpl.
        split.
        -- intros Heq; lia.
        -- intros _; reflexivity.
      * try rewrite Zlength_app; simpl; lia.
  - rewrite Zlength_sublist by lia. lia.
  - try rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed. 

Lemma proof_of_array_replace_k_return_wit_1 : array_replace_k_return_wit_1.
Proof.
  pre_process.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  assert (l2 = nil).
  {
    apply Zlength_nil_inv.
    lia.
  }
  subst l2.
  rewrite app_nil_r.
  Exists l1.
  entailer!.
  intros i Hi.
  match goal with
  | Hprefix : forall t : Z,
      ((0 <= t) /\ (t < Zlength l1)) ->
      ((Znth t l 0 = old_k_pre -> Znth t l1 0 = new_k_pre) /\
       (Znth t l 0 <> old_k_pre -> Znth t l1 0 = Znth t l 0)) |- _ =>
      apply Hprefix; lia
  end.
Qed. 
