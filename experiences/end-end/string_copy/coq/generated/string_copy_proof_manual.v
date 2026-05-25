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
From SimpleC.EE.CAV.verify_20260422_235720_string_copy Require Import string_copy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_copy_entail_wit_1 : string_copy_entail_wit_1.
Proof.
  pre_process.
  Exists d nil.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n + 1) d)).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n + 1) d)
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  entailer!.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma proof_of_string_copy_entail_wit_2 : string_copy_entail_wit_2.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n + 1)
                (replace_Znth i (Znth i (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n + 1)
                (replace_Znth i (Znth i (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))).
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hlen_nat : Z.of_nat (Datatypes.length l) = n).
  {
    rewrite <- Zlength_correct.
    exact Hlen_l.
  }
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      assert (Hlen_l1_2 : Zlength l1_2 = n) by lia.
      rewrite Hlen_l1_2 in H.
      rewrite app_Znth2 in H by lia.
      replace (n - Zlength l) with 0 in H by lia.
      cbn in H.
      exfalso.
      apply H.
      reflexivity.
  }
  destruct d1_2 eqn:Hd1.
  - rewrite Zlength_nil in H4. lia.
  - simpl in H4.
  assert (Hdst :
    replace_Znth i (Znth i (l ++ 0 :: nil) 0) (l1_2 ++ z :: l0) =
    (l1_2 ++ cons (Znth i l 0) nil) ++ l0).
  {
    rewrite app_Znth1 by lia.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i - Zlength l1_2) with 0 by lia.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  Exists l0 (l1_2 ++ cons (Znth i l 0) nil).
  rewrite Hdst.
  assert (Hlen_l1_new :
    Zlength (l1_2 ++ cons (Znth i l 0) nil) = i + 1).
  {
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hlen_l0 : Zlength l0 = n + 1 - (i + 1)).
  {
    rewrite Zlength_cons in H4.
    lia.
  }
  assert (Hprefix_new :
    forall k : Z,
      0 <= k < i + 1 ->
      Znth k (l1_2 ++ cons (Znth i l 0) nil) 0 = Znth k l 0).
  {
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      apply H6.
      lia.
    - assert (k = i) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength l1_2) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_string_copy_return_wit_1 : string_copy_return_wit_1.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)))
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)))).
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hlen_nat : Z.of_nat (Datatypes.length l) = n).
  {
    rewrite <- Zlength_correct.
    exact Hlen_l.
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
  assert (Hl1_eq_l : l1 = l).
  {
    apply (proj2 (list_eq_ext 0 l1 l)).
    split.
    - lia.
    - intros k Hk.
      apply H6.
      lia.
  }
  subst l1.
  assert (Hd1_single : exists x, d1 = x :: nil).
  {
    destruct d1.
    - rewrite Zlength_nil in H4. lia.
    - rewrite Zlength_cons in H4.
      destruct d1.
      + eexists. reflexivity.
      + repeat rewrite Zlength_cons in H4.
        pose proof Zlength_nonneg d1.
        lia.
  }
  destruct Hd1_single.
  subst d1.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (n - Zlength l) with 0 by lia.
  unfold replace_Znth.
  replace (Z.to_nat (Zlength l - Zlength l)) with 0%nat by lia.
  simpl.
  entailer!.
Qed.
