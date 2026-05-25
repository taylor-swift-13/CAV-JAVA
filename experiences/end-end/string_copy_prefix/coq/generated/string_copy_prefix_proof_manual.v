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
From SimpleC.EE.CAV.verify_20260423_000831_string_copy_prefix Require Import string_copy_prefix_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_copy_prefix_entail_wit_1 : string_copy_prefix_entail_wit_1.
Proof.
  pre_process.
  Exists d nil.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (k_pre + 1) d)).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (k_pre + 1) d)
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  entailer!.
Qed.

Lemma proof_of_string_copy_prefix_entail_wit_2 : string_copy_prefix_entail_wit_2.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (k_pre + 1)
                (replace_Znth i_2 (Znth i_2 (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (k_pre + 1)
                (replace_Znth i_2 (Znth i_2 (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))).
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  destruct d1_2 eqn:Hd1.
  - match goal with
    | Hnil : Zlength nil = _ |- _ =>
        rewrite Zlength_nil in Hnil; lia
    end.
  - assert (Hlen_d1_cons : Zlength (z :: l0) = k_pre + 1 - i_2).
    {
      match goal with
      | Hlen : Zlength (z :: l0) = k_pre + 1 - i_2 |- _ =>
          exact Hlen
      end.
    }
  rewrite Zlength_cons in Hlen_d1_cons.
  assert (Hdst :
    replace_Znth i_2 (Znth i_2 (l ++ 0 :: nil) 0) (l1_2 ++ z :: l0) =
    (l1_2 ++ cons (Znth i_2 l 0) nil) ++ l0).
  {
    rewrite app_Znth1 by lia.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i_2 - Zlength l1_2) with 0 by lia.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  Exists l0 (l1_2 ++ cons (Znth i_2 l 0) nil).
  rewrite Hdst.
  assert (Hlen_l1_new :
    Zlength (l1_2 ++ cons (Znth i_2 l 0) nil) = i_2 + 1).
  {
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hlen_l0 : Zlength l0 = k_pre + 1 - (i_2 + 1)).
  {
    lia.
  }
  assert (Hprefix_new :
    forall k : Z,
      0 <= k < i_2 + 1 ->
      Znth k (l1_2 ++ cons (Znth i_2 l 0) nil) 0 = Znth k l 0).
  {
    intros k Hk.
    destruct (Z_lt_ge_dec k i_2) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      apply H10.
      lia.
    - assert (k = i_2) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      replace (i_2 - Zlength l1_2) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_string_copy_prefix_return_wit_1 : string_copy_prefix_return_wit_1.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (k_pre + 1) (replace_Znth k_pre 0 (l1 ++ d1)))
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (k_pre + 1) (replace_Znth k_pre 0 (l1 ++ d1)))).
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_eq_k : i_2 = k_pre) by lia.
  subst i_2.
  assert (Hl1_eq_prefix : l1 = sublist 0 k_pre l).
  {
    apply (proj2 (list_eq_ext 0 l1 (sublist 0 k_pre l))).
    split.
    - rewrite Zlength_sublist by lia.
      lia.
    - intros k Hk.
      rewrite Znth_sublist by lia.
      replace (k + 0) with k by lia.
      apply H10.
      lia.
  }
  subst l1.
  assert (Hd1_single : exists x, d1 = x :: nil).
  {
    destruct d1.
    - match goal with
      | Hnil : Zlength nil = _ |- _ =>
          rewrite Zlength_nil in Hnil; lia
      end.
    - match goal with
      | Hcons : Zlength (z :: d1) = _ |- _ =>
          pose proof Hcons as Hlen_d1_cons;
          rewrite Zlength_cons in Hlen_d1_cons
      end.
      destruct d1.
      + eexists. reflexivity.
      + rewrite Zlength_cons in Hlen_d1_cons.
        pose proof Zlength_nonneg d1.
        lia.
  }
  destruct Hd1_single as [x Hx].
  subst d1.
  rewrite replace_Znth_app_r by (rewrite Zlength_sublist by lia; lia).
  rewrite replace_Znth_nothing by (rewrite Zlength_sublist by lia; lia).
  replace (k_pre - Zlength (sublist 0 k_pre l)) with 0 by
    (rewrite Zlength_sublist by lia; lia).
  unfold replace_Znth.
  replace (Z.to_nat 0) with 0%nat by lia.
  simpl.
  entailer!.
Qed.
