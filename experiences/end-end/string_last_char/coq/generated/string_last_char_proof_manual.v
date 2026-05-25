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
From SimpleC.EE.CAV.verify_20260423_120929_string_last_char Require Import string_last_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma app_zero_at_length :
  forall (l : list Z) (n : Z),
    Zlength l = n ->
    Znth n (l ++ 0 :: nil) 0 = 0.
Proof.
  intros l n Hlen.
  rewrite app_Znth2 by lia.
  rewrite Hlen.
  replace (n - n) with 0 by lia.
  reflexivity.
Qed.

Lemma app_zero_nonzero_implies_lt :
  forall (l : list Z) (n k : Z),
    Zlength l = n ->
    0 <= k ->
    k <= n ->
    Znth k (l ++ 0 :: nil) 0 <> 0 ->
    k < n.
Proof.
  intros l n k Hlen Hk0 Hkle Hnz.
  destruct (Z_lt_ge_dec k n) as [Hlt | Hge].
  - exact Hlt.
  - assert (k = n) by lia.
    subst k.
    rewrite app_zero_at_length in Hnz by exact Hlen.
    contradiction Hnz; reflexivity.
Qed.

Lemma app_zero_eq_zero_implies_length :
  forall (l : list Z) (n k : Z),
    Zlength l = n ->
    0 <= k ->
    k <= n ->
    (forall j : Z, 0 <= j /\ j < n -> Znth j l 0 <> 0) ->
    Znth k (l ++ 0 :: nil) 0 = 0 ->
    k = n.
Proof.
  intros l n k Hlen Hk0 Hkle Hnonzero Hz.
  destruct (Z_lt_ge_dec k n) as [Hlt | Hge].
  - rewrite app_Znth1 in Hz by lia.
    specialize (Hnonzero k (conj Hk0 Hlt)).
    contradiction Hnonzero; exact Hz.
  - lia.
Qed.

Lemma app_zero_last_value :
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    0 < n ->
    i = n - 1 ->
    Znth i (l ++ 0 :: nil) 0 = Znth (n - 1) l 0.
Proof.
  intros l n i Hlen Hn Hi.
  subst i.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma proof_of_string_last_char_entail_wit_2 : string_last_char_entail_wit_2.
Proof.
  unfold string_last_char_entail_wit_2.
  pre_process.
  assert (Hi1_lt : i + 1 < n).
  {
    apply app_zero_nonzero_implies_lt with (l := l); lia.
  }
  entailer!.
Qed. 

Lemma proof_of_string_last_char_entail_wit_3 : string_last_char_entail_wit_3.
Proof.
  unfold string_last_char_entail_wit_3.
  pre_process.
  assert (Hi1_eq : i + 1 = n).
  {
    apply app_zero_eq_zero_implies_length with (l := l); try lia; eauto.
  }
  entailer!.
Qed. 

Lemma proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Proof.
  unfold string_last_char_return_wit_1.
  pre_process.
  rewrite (app_zero_last_value l n i) by lia.
  entailer!.
Qed. 
