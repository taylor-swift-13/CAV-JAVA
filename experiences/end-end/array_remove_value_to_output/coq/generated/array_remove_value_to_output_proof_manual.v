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
From SimpleC.EE.CAV.verify_20260422_071205_array_remove_value_to_output Require Import array_remove_value_to_output_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_remove_value_to_output.
Local Open Scope sac.
Import ListNotations.

Lemma arvo_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros.
  revert i v.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl; reflexivity.
Qed.

Lemma arvo_nth_replace_nth_eq:
  forall T (l: list T) i v u,
    (i < length l)%nat ->
    nth i (replace_nth i v l) u = v.
Proof.
  intros.
  revert i H.
  induction l; intros; simpl in *.
  - lia.
  - destruct i; simpl.
    + reflexivity.
    + apply IHl; lia.
Qed.

Lemma arvo_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros.
  revert a b H.
  induction l; intros.
  - destruct a; destruct b; try lia; reflexivity.
  - destruct a0; simpl.
    + destruct b; simpl; [lia | reflexivity].
    + destruct b; simpl; try reflexivity.
      assert (a0 <> b)%nat by lia.
      apply IHl; easy.
Qed.

Lemma arvo_replace_Znth_length {A: Type}:
  forall n (a: A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite arvo_replace_nth_length.
  reflexivity.
Qed.

Lemma arvo_Znth_replace_Znth_same :
  forall (n: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply arvo_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma arvo_Znth_replace_Znth_other :
  forall (n: Z) (m: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply arvo_nth_replace_nth_other.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma arvo_spec_snoc_keep :
  forall xs x k,
    x <> k ->
    array_remove_value_to_output_spec (xs ++ [x]) k =
    array_remove_value_to_output_spec xs k ++ [x].
Proof.
  induction xs; intros x k Hx; simpl.
  - destruct (Z.eq_dec x k); [contradiction | reflexivity].
  - destruct (Z.eq_dec a k); simpl; rewrite IHxs by exact Hx; reflexivity.
Qed.

Lemma arvo_spec_snoc_drop :
  forall xs x k,
    x = k ->
    array_remove_value_to_output_spec (xs ++ [x]) k =
    array_remove_value_to_output_spec xs k.
Proof.
  induction xs; intros x k Hx; simpl.
  - subst x. destruct (Z.eq_dec k k); [reflexivity | contradiction].
  - destruct (Z.eq_dec a k); simpl; rewrite IHxs by exact Hx; reflexivity.
Qed.

Lemma arvo_spec_length_bound :
  forall xs k,
    0 <= Zlength (array_remove_value_to_output_spec xs k) <= Zlength xs.
Proof.
  induction xs; intros k.
  - simpl. rewrite Zlength_nil. lia.
  - simpl. destruct (Z.eq_dec a k); rewrite Zlength_cons; try rewrite Zlength_cons; specialize (IHxs k); lia.
Qed.

Lemma arvo_prefix_tail_rebuild :
  forall (spec lout: list Z) n write,
    Zlength lout = n ->
    Zlength spec = write ->
    0 <= write <= n ->
    (forall p, 0 <= p /\ p < write -> Znth p lout 0 = Znth p spec 0) ->
    lout = spec ++ sublist write n lout.
Proof.
  intros spec lout n write Hlout Hspec Hrange Hprefix.
  apply (proj2 (list_eq_ext 0 lout (spec ++ sublist write n lout))).
  split.
  - rewrite Zlength_app, Zlength_sublist by lia.
    lia.
  - intros p Hp.
    destruct (Z_lt_ge_dec p write) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      apply Hprefix; lia.
    + rewrite app_Znth2 by lia.
      rewrite Znth_sublist by lia.
      replace (p - Zlength spec + write) with p by lia.
      reflexivity.
Qed.

Lemma proof_of_array_remove_value_to_output_entail_wit_1 : array_remove_value_to_output_entail_wit_1.
Proof.
  pre_process.
  Exists lo.
  entailer!.
Qed. 

Lemma proof_of_array_remove_value_to_output_entail_wit_2_1 : array_remove_value_to_output_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hi_l : Znth i la 0 = Znth i la 0) by reflexivity.
  assert (Hi_keep : Znth i la 0 <> k_pre) by congruence.
  assert (Hsnoc :
    sublist 0 (i + 1) la = sublist 0 i la ++ [Znth i la 0]).
  {
    rewrite (sublist_split 0 (i + 1) i la) by (pose proof (Zlength_correct la); lia).
    rewrite (sublist_single i la 0) by (pose proof (Zlength_correct la); lia).
    reflexivity.
  }
  assert (Hspec_next :
    array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre =
    array_remove_value_to_output_spec (sublist 0 i la) k_pre ++ [Znth i la 0]).
  {
    rewrite Hsnoc.
    apply arvo_spec_snoc_keep.
    exact Hi_keep.
  }
  Exists (replace_Znth write (Znth i la 0) lout_2).
  entailer!.
  - intros p Hp.
    rewrite arvo_Znth_replace_Znth_other; try lia.
    apply H10; lia.
  - intros p Hp.
    rewrite Hspec_next.
    destruct Hp as [Hp0 Hp1].
    destruct (Z_lt_ge_dec p write) as [Hlt | Hge].
    + rewrite arvo_Znth_replace_Znth_other; try lia.
      rewrite app_Znth1 by lia.
      apply H9; lia.
    + assert (p = write) by lia.
      subst p.
      rewrite arvo_Znth_replace_Znth_same by lia.
      rewrite app_Znth2 by lia.
      replace (write - Zlength (array_remove_value_to_output_spec (sublist 0 i la) k_pre)) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
  - rewrite Hspec_next.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite arvo_replace_Znth_length.
    exact H7.
Qed. 

Lemma proof_of_array_remove_value_to_output_entail_wit_2_2 : array_remove_value_to_output_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_drop : Znth i la 0 = k_pre) by congruence.
  assert (Hsnoc :
    sublist 0 (i + 1) la = sublist 0 i la ++ [Znth i la 0]).
  {
    rewrite (sublist_split 0 (i + 1) i la) by (pose proof (Zlength_correct la); lia).
    rewrite (sublist_single i la 0) by (pose proof (Zlength_correct la); lia).
    reflexivity.
  }
  assert (Hspec_next :
    array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre =
    array_remove_value_to_output_spec (sublist 0 i la) k_pre).
  {
    rewrite Hsnoc.
    apply arvo_spec_snoc_drop.
    exact Hi_drop.
  }
  Exists lout_2.
  entailer!.
  - intros p Hp.
    rewrite Hspec_next.
    apply H9; lia.
  - rewrite Hspec_next.
    exact H8.
Qed. 

Lemma proof_of_array_remove_value_to_output_entail_wit_3 : array_remove_value_to_output_entail_wit_3.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hsub : sublist 0 n_pre la = la).
  {
    rewrite H4.
    apply sublist_self.
    reflexivity.
  }
  Exists lout_2.
  entailer!.
  - intros p Hp.
    rewrite Hsub in H8.
    apply H8; lia.
  - rewrite Hsub in H7.
    exact H7.
Qed. 

Lemma proof_of_array_remove_value_to_output_return_wit_1 : array_remove_value_to_output_return_wit_1.
Proof.
  pre_process.
  Exists (sublist write n_pre lout).
  assert (Hspec_len : Zlength (array_remove_value_to_output_spec la k_pre) = write) by lia.
  assert (Hout_rebuild :
    lout = array_remove_value_to_output_spec la k_pre ++ sublist write n_pre lout).
  {
    apply arvo_prefix_tail_rebuild with (n := n_pre) (write := write); try lia.
    intros p Hp.
    apply H5; lia.
  }
  rewrite <- Hout_rebuild.
  entailer!.
  rewrite Zlength_sublist by lia.
  lia.
Qed. 
