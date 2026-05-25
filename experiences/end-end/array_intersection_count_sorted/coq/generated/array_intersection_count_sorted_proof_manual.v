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
Require Import array_intersection_count_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_intersection_count_sorted.
Local Open Scope sac.

Lemma array_intersection_sublist_cons :
  forall (l : list Z) (lo hi : Z),
    0 <= lo ->
    lo < hi ->
    hi <= Zlength l ->
    sublist lo hi l = Znth lo l 0 :: sublist (lo + 1) hi l.
Proof.
  intros l lo hi Hlo Hlt Hhi.
  assert (Hhi_len : hi <= Z.of_nat (length l)).
  {
    rewrite <- Zlength_correct.
    exact Hhi.
  }
  rewrite (sublist_split lo hi (lo + 1) l) by lia.
  rewrite (sublist_single lo l 0) by (rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.

Lemma array_intersection_spec_nil_r :
  forall (l : list Z),
    array_intersection_count_sorted_spec l nil = 0.
Proof.
  induction l; simpl; auto.
Qed.

Lemma array_intersection_step_eq :
  forall la lb i n j m,
    0 <= i ->
    i < n ->
    n <= Zlength la ->
    0 <= j ->
    j < m ->
    m <= Zlength lb ->
    Znth i la 0 = Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      1 + array_intersection_count_sorted_spec
            (sublist (i + 1) n la) (sublist (j + 1) m lb).
Proof.
  intros la lb i n j m Hi0 Hin Hn Hj0 Hjm Hm Heq.
  rewrite (array_intersection_sublist_cons la i n) by lia.
  rewrite (array_intersection_sublist_cons lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)) as [Heq' | Hneq].
  - reflexivity.
  - lia.
Qed.

Lemma array_intersection_step_lt :
  forall la lb i n j m,
    0 <= i ->
    i < n ->
    n <= Zlength la ->
    0 <= j ->
    j < m ->
    m <= Zlength lb ->
    Znth i la 0 < Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      array_intersection_count_sorted_spec (sublist (i + 1) n la) (sublist j m lb).
Proof.
  intros la lb i n j m Hi0 Hin Hn Hj0 Hjm Hm Hlt.
  rewrite (array_intersection_sublist_cons la i n) by lia.
  rewrite (array_intersection_sublist_cons lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)) as [Heq | Hneq].
  - lia.
  - destruct (Z.ltb_spec0 (Znth i la 0) (Znth j lb 0)) as [Hlt' | Hnlt].
    + reflexivity.
    + lia.
Qed.

Lemma array_intersection_step_gt :
  forall la lb i n j m,
    0 <= i ->
    i < n ->
    n <= Zlength la ->
    0 <= j ->
    j < m ->
    m <= Zlength lb ->
    Znth i la 0 > Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      array_intersection_count_sorted_spec (sublist i n la) (sublist (j + 1) m lb).
Proof.
  intros la lb i n j m Hi0 Hin Hn Hj0 Hjm Hm Hgt.
  rewrite (array_intersection_sublist_cons la i n) by lia.
  rewrite (array_intersection_sublist_cons lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)) as [Heq | Hneq].
  - lia.
  - destruct (Z.ltb_spec0 (Znth i la 0) (Znth j lb 0)) as [Hlt | Hnlt].
    + lia.
    + reflexivity.
Qed.

Lemma proof_of_array_intersection_count_sorted_entail_wit_1 : array_intersection_count_sorted_entail_wit_1.
Proof.
  unfold array_intersection_count_sorted_entail_wit_1.
  intros.
  entailer!.
  rewrite sublist_self by lia.
  rewrite sublist_self by lia.
  reflexivity.
Qed. 

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_1 : array_intersection_count_sorted_entail_wit_2_1.
Proof.
  unfold array_intersection_count_sorted_entail_wit_2_1.
  intros.
  entailer!.
  match goal with
  | Hspec : count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb) =
            array_intersection_count_sorted_spec la lb |- _ =>
      rewrite <- Hspec
  end.
  rewrite (array_intersection_step_gt la lb i_3 n_pre j_3 m_pre) by lia.
  reflexivity.
Qed. 

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_2 : array_intersection_count_sorted_entail_wit_2_2.
Proof.
  unfold array_intersection_count_sorted_entail_wit_2_2.
  intros.
  entailer!.
  match goal with
  | Hspec : count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb) =
            array_intersection_count_sorted_spec la lb |- _ =>
      rewrite <- Hspec
  end.
  rewrite (array_intersection_step_lt la lb i_3 n_pre j_3 m_pre) by lia.
  reflexivity.
Qed. 

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_3 : array_intersection_count_sorted_entail_wit_2_3.
Proof.
  unfold array_intersection_count_sorted_entail_wit_2_3.
  intros.
  entailer!.
  match goal with
  | Hspec : count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb) =
            array_intersection_count_sorted_spec la lb |- _ =>
      rewrite <- Hspec
  end.
  rewrite (array_intersection_step_eq la lb i_3 n_pre j_3 m_pre) by lia.
  lia.
Qed. 

Lemma proof_of_array_intersection_count_sorted_return_wit_1 : array_intersection_count_sorted_return_wit_1.
Proof.
  unfold array_intersection_count_sorted_return_wit_1.
  intros.
  entailer!.
  assert (j_3 = m_pre) by lia.
  subst j_3.
  replace (sublist m_pre m_pre lb) with (@nil Z) in H16
    by (rewrite sublist_nil by lia; reflexivity).
  rewrite array_intersection_spec_nil_r in H16.
  lia.
Qed. 

Lemma proof_of_array_intersection_count_sorted_return_wit_2 : array_intersection_count_sorted_return_wit_2.
Proof.
  unfold array_intersection_count_sorted_return_wit_2.
  intros.
  entailer!.
  assert (i_3 = n_pre) by lia.
  subst i_3.
  replace (sublist n_pre n_pre la) with (@nil Z) in H15
    by (rewrite sublist_nil by lia; reflexivity).
  simpl in H15.
  lia.
Qed. 
