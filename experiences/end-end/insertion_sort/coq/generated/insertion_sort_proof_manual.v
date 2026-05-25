Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
From AUXLib Require Import ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260422_174132_insertion_sort Require Import insertion_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import insertion_sort.
Local Open Scope sac.

Lemma insertion_sort_sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  rewrite firstn_all2 by lia.
  reflexivity.
Qed.

Lemma insertion_sort_replace_nth_length:
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

Lemma insertion_sort_replace_Znth_length {A: Type}:
  forall (l:list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n a.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite insertion_sort_replace_nth_length.
  reflexivity.
Qed.

Lemma insertion_sort_nth_a_replace_nth_b:
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

Lemma insertion_sort_nth_replace_nth_eq:
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

Lemma insertion_sort_Znth_replace_Znth_eq :
  forall {A} n (l : list A) v d,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply insertion_sort_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma insertion_sort_Znth_replace_Znth_other :
  forall {A} n m (l : list A) v d,
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply insertion_sort_nth_a_replace_nth_b.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma insertion_sort_replace_Znth_last :
  forall {A} (p : list A) y x,
    replace_Znth (Zlength p) x (p ++ y :: nil) = p ++ x :: nil.
Proof.
  intros A p.
  induction p; intros y x.
  - simpl. reflexivity.
  - rewrite Zlength_cons.
    simpl.
    pose proof (Zlength_nonneg p).
    rewrite replace_Znth_cons by lia.
    replace (Z.succ (Zlength p) - 1) with (Zlength p) by lia.
    rewrite IHp.
    reflexivity.
Qed.

Lemma insertion_sort_lcur_Znth_base :
  forall n j i (l_base l_cur : list Z),
    0 <= j ->
    j < i ->
    i < n ->
    n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    Znth j l_cur 0 = Znth j l_base 0.
Proof.
  intros n j i l_base l_cur Hj0 Hji Hin Hlen Hcur.
  subst l_cur.
  rewrite app_Znth1.
  - rewrite Znth_sublist0 by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma insertion_sort_shift_list_eq :
  forall n j i (l_base l_cur : list Z),
    0 <= j ->
    j < i ->
    i < n ->
    n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    replace_Znth (j + 1) (Znth j l_cur 0) l_cur =
      sublist 0 (j + 1) l_base ++
      sublist j i l_base ++ sublist (i + 1) n l_base.
Proof.
  intros n j i l_base l_cur Hj0 Hji Hin Hlen Hcur.
  assert (Hz : Znth j l_cur 0 = Znth j l_base 0).
  { eapply insertion_sort_lcur_Znth_base; eauto. }
  subst l_cur.
  rewrite Hz.
  rewrite (sublist_split 0 (j + 2) (j + 1) l_base)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  replace (j + 2) with (j + 1 + 1) by lia.
  rewrite (sublist_single (j + 1) l_base 0)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  set (P := sublist 0 (j + 1) l_base).
  set (y := Znth (j + 1) l_base 0).
  set (Q := sublist (j + 1) i l_base).
  set (R := sublist (i + 1) n l_base).
  replace ((P ++ y :: nil) ++ Q ++ R) with ((P ++ y :: nil) ++ (Q ++ R))
    by (rewrite app_assoc; reflexivity).
  rewrite replace_Znth_app_l.
  2:{ lia. }
  2:{
    subst P. rewrite Zlength_app, Zlength_sublist by lia.
    simpl. rewrite Zlength_cons, Zlength_nil. lia.
  }
  replace (j + 1) with (Zlength P).
  2:{ subst P. rewrite Zlength_sublist by lia; lia. }
  rewrite insertion_sort_replace_Znth_last.
  subst P Q R.
  repeat rewrite <- app_assoc.
  f_equal.
  rewrite (sublist_split j i (j + 1) l_base)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  rewrite (sublist_single j l_base 0)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  reflexivity.
Qed.

Lemma insertion_sort_final_list_eq :
  forall n j i (l_base l_cur : list Z) key,
    -1 <= j ->
    j < i ->
    i < n ->
    n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    replace_Znth (j + 1) key l_cur =
      sublist 0 (j + 1) l_base ++ key :: nil ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base.
Proof.
  intros n j i l_base l_cur key Hjlow Hji Hin Hlen Hcur.
  subst l_cur.
  rewrite (sublist_split 0 (j + 2) (j + 1) l_base)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  replace (j + 2) with (j + 1 + 1) by lia.
  rewrite (sublist_single (j + 1) l_base 0)
    by (try rewrite <- Zlength_correct; try rewrite <- Hlen; lia).
  set (P := sublist 0 (j + 1) l_base).
  set (y := Znth (j + 1) l_base 0).
  set (Q := sublist (j + 1) i l_base).
  set (R := sublist (i + 1) n l_base).
  replace ((P ++ y :: nil) ++ Q ++ R) with ((P ++ y :: nil) ++ (Q ++ R))
    by (rewrite app_assoc; reflexivity).
  rewrite replace_Znth_app_l.
  2:{ lia. }
  2:{
    subst P. rewrite Zlength_app, Zlength_sublist by lia.
    simpl. rewrite Zlength_cons, Zlength_nil. lia.
  }
  replace (j + 1) with (Zlength P).
  2:{ subst P. rewrite Zlength_sublist by lia; lia. }
  rewrite insertion_sort_replace_Znth_last.
  subst P Q R.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma insertion_sort_final_Znth_left :
  forall n j i (l_base l_cur : list Z) key p,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    0 <= p <= j ->
    Znth p (replace_Znth (j + 1) key l_cur) 0 = Znth p l_base 0.
Proof.
  intros.
  rewrite (insertion_sort_final_list_eq n j i l_base l_cur key) by auto.
  rewrite app_Znth1.
  - rewrite Znth_sublist0 by lia. reflexivity.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma insertion_sort_final_Znth_key :
  forall n j i (l_base l_cur : list Z) key,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    Znth (j + 1) (replace_Znth (j + 1) key l_cur) 0 = key.
Proof.
  intros.
  rewrite (insertion_sort_final_list_eq n j i l_base l_cur key) by auto.
  rewrite app_Znth2.
  2:{ rewrite Zlength_sublist by lia; lia. }
  replace (j + 1 - Zlength (sublist 0 (j + 1) l_base)) with 0
    by (rewrite Zlength_sublist by lia; lia).
  simpl. reflexivity.
Qed.

Lemma insertion_sort_final_Znth_mid :
  forall n j i (l_base l_cur : list Z) key p,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    j + 1 < p < i + 1 ->
    Znth p (replace_Znth (j + 1) key l_cur) 0 = Znth (p - 1) l_base 0.
Proof.
  intros.
  rewrite (insertion_sort_final_list_eq n j i l_base l_cur key) by auto.
  set (P := sublist 0 (j + 1) l_base).
  set (Q := sublist (j + 1) i l_base).
  set (R := sublist (i + 1) n l_base).
  rewrite app_Znth2.
  2:{ subst P. rewrite Zlength_sublist by lia. lia. }
  replace (p - Zlength P) with (p - (j + 1)).
  2:{ subst P. rewrite Zlength_sublist by lia. lia. }
  rewrite Znth_cons by lia.
  replace (p - (j + 1) - 1) with (p - (j + 2)) by lia.
  simpl.
  subst P Q R.
  rewrite app_Znth1.
  - rewrite Znth_sublist by lia.
    replace (j + 1 + (p - (j + 2))) with (p - 1) by lia.
    replace (p - (j + 2) + (j + 1)) with (p - 1) by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma insertion_sort_final_Znth_after :
  forall n j i (l_base l_cur : list Z) key p,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    i + 1 <= p < n ->
    Znth p (replace_Znth (j + 1) key l_cur) 0 = Znth p l_base 0.
Proof.
  intros.
  rewrite (insertion_sort_final_list_eq n j i l_base l_cur key) by auto.
  set (P := sublist 0 (j + 1) l_base).
  set (Q := sublist (j + 1) i l_base).
  set (R := sublist (i + 1) n l_base).
  rewrite app_Znth2.
  2:{ subst P. rewrite Zlength_sublist by lia. lia. }
  replace (p - Zlength P) with (p - (j + 1)).
  2:{ subst P. rewrite Zlength_sublist by lia. lia. }
  rewrite Znth_cons by lia.
  replace (p - (j + 1) - 1) with (p - (j + 2)) by lia.
  simpl.
  rewrite app_Znth2.
  2:{ subst Q. rewrite Zlength_sublist by lia. lia. }
  subst P Q R.
  replace (p - (j + 2) - Zlength (sublist (j + 1) i l_base))
    with (p - (i + 1)).
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite Znth_sublist by lia.
  replace (i + 1 + (p - (i + 1))) with p by lia.
  replace (p - (i + 1) + (i + 1)) with p by lia.
  reflexivity.
Qed.

Lemma insertion_sort_final_Zlength :
  forall n j i (l_base l_cur : list Z) key,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    Zlength (replace_Znth (j + 1) key l_cur) = n.
Proof.
  intros.
  rewrite insertion_sort_replace_Znth_length.
  subst l_cur.
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma insertion_sort_final_perm :
  forall n j i (l_base l_cur : list Z) key,
    -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    key = Znth i l_base 0 ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    Permutation l_base (replace_Znth (j + 1) key l_cur).
Proof.
  intros n j i l_base l_cur key Hjlow Hji Hin Hlen Hkey Hcur.
  rewrite (insertion_sort_final_list_eq n j i l_base l_cur key) by auto.
  assert (Hbase :
    l_base =
      sublist 0 (j + 1) l_base ++
      sublist (j + 1) i l_base ++
      key :: sublist (i + 1) n l_base).
  {
    replace n with (Zlength l_base) by lia.
    rewrite <- insertion_sort_sublist_full_Zlength at 1.
    rewrite (sublist_split 0 (Zlength l_base) (j + 1) l_base)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_split (j + 1) (Zlength l_base) i l_base)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_split i (Zlength l_base) (i + 1) l_base)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single i l_base 0)
      by (try rewrite <- Zlength_correct; lia).
    rewrite <- Hkey.
    repeat rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hbase at 1.
  repeat rewrite <- app_assoc.
  apply Permutation_app_head.
  simpl.
  symmetry.
  apply Permutation_middle.
Qed.

Lemma insertion_sort_final_adj_ge :
  forall n j i (l_base l_cur : list Z) key,
    0 <= j -> j < i -> i < n -> n = Zlength l_base ->
    key = Znth i l_base 0 ->
    Znth j l_cur 0 <= key ->
    (forall k, 0 <= k /\ k + 1 < i ->
      Znth k l_base 0 <= Znth (k + 1) l_base 0) ->
    (forall k, j < k /\ k < i -> key < Znth k l_base 0) ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    forall k, 0 <= k /\ k + 1 < i + 1 ->
      Znth k (replace_Znth (j + 1) key l_cur) 0 <=
      Znth (k + 1) (replace_Znth (j + 1) key l_cur) 0.
Proof.
  intros n j i l_base l_cur key Hj0 Hji Hin Hlen Hkey Hguard Hadj Hshift Hcur k Hk.
  destruct (Z_lt_ge_dec k j) as [Hlt|Hge].
  - rewrite insertion_sort_final_Znth_left with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
    rewrite insertion_sort_final_Znth_left with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
    apply Hadj. lia.
  - destruct (Z.eq_dec k j) as [->|Hneqj].
    + rewrite insertion_sort_final_Znth_left with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
      rewrite insertion_sort_final_Znth_key with (n := n) (i := i) (l_base := l_base) by lia || eauto.
      rewrite <- (insertion_sort_lcur_Znth_base n j i l_base l_cur) by lia || eauto.
      exact Hguard.
    + assert (Hgtj : j < k) by lia.
      destruct (Z.eq_dec k (j + 1)) as [->|Hneqj1].
      * rewrite insertion_sort_final_Znth_key with (n := n) (i := i) (l_base := l_base) by lia || eauto.
        rewrite insertion_sort_final_Znth_mid with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
        apply Z.lt_le_incl. apply Hshift. lia.
      * assert (Hgtj1 : j + 1 < k) by lia.
        rewrite insertion_sort_final_Znth_mid with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
        destruct (Z.eq_dec (k + 1) (i + 1)) as [Hlast|Hnotlast].
        -- lia.
        -- rewrite insertion_sort_final_Znth_mid with (n := n) (j := j) (i := i) (l_base := l_base) by lia || eauto.
           replace (k + 1 - 1) with k by lia.
           replace k with (k - 1 + 1) by lia.
           replace (k - 1 + 1 - 1) with (k - 1) by lia.
           apply (Hadj (k - 1)). lia.
Qed.

Lemma insertion_sort_final_adj_neg :
  forall n j i (l_base l_cur : list Z) key,
    j < 0 -> -1 <= j -> j < i -> i < n -> n = Zlength l_base ->
    key = Znth i l_base 0 ->
    (forall k, 0 <= k /\ k + 1 < i ->
      Znth k l_base 0 <= Znth (k + 1) l_base 0) ->
    (forall k, j < k /\ k < i -> key < Znth k l_base 0) ->
    l_cur =
      sublist 0 (j + 2) l_base ++
      sublist (j + 1) i l_base ++ sublist (i + 1) n l_base ->
    forall k, 0 <= k /\ k + 1 < i + 1 ->
      Znth k (replace_Znth (j + 1) key l_cur) 0 <=
      Znth (k + 1) (replace_Znth (j + 1) key l_cur) 0.
Proof.
  intros n j i l_base l_cur key Hjneg Hjlow Hji Hin Hlen Hkey Hadj Hshift Hcur k Hk.
  assert (Hj : j = -1) by lia.
  subst j.
  destruct (Z.eq_dec k 0) as [->|Hk0].
  - rewrite insertion_sort_final_Znth_key with (n := n) (j := -1) (i := i) (l_base := l_base) by lia || eauto.
    destruct (Z.eq_dec i 0) as [Hi0|Hi0].
    + lia.
    + rewrite insertion_sort_final_Znth_mid with (n := n) (j := -1) (i := i) (l_base := l_base) by lia || eauto.
      apply Z.lt_le_incl. apply Hshift. lia.
  - assert (0 < k) by lia.
    rewrite insertion_sort_final_Znth_mid with (n := n) (j := -1) (i := i) (l_base := l_base) by lia || eauto.
    destruct (Z.eq_dec (k + 1) (i + 1)) as [Hlast|Hnotlast].
    + lia.
    + rewrite insertion_sort_final_Znth_mid with (n := n) (j := -1) (i := i) (l_base := l_base) by lia || eauto.
      replace (k + 1 - 1) with k by lia.
      replace k with (k - 1 + 1) by lia.
      replace (k - 1 + 1 - 1) with (k - 1) by lia.
      apply (Hadj (k - 1)). lia.
Qed.

Lemma insertion_sort_adjacent_tail :
  forall h l,
    (forall k, 0 <= k /\ k + 1 < Zlength (h :: l) ->
      Znth k (h :: l) 0 <= Znth (k + 1) (h :: l) 0) ->
    forall k, 0 <= k /\ k + 1 < Zlength l ->
      Znth k l 0 <= Znth (k + 1) l 0.
Proof.
  intros h l Hadj k Hk.
  specialize (Hadj (k + 1)).
  assert (Hadj' : Znth (k + 1) (h :: l) 0 <=
                  Znth (k + 1 + 1) (h :: l) 0).
  { apply Hadj. rewrite Zlength_cons. lia. }
  rewrite (Znth_cons (k + 1) h l 0) in Hadj' by lia.
  rewrite (Znth_cons (k + 1 + 1) h l 0) in Hadj' by lia.
  replace (k + 1 - 1) with k in Hadj' by lia.
  replace (k + 1 + 1 - 1) with (k + 1) in Hadj' by lia.
  exact Hadj'.
Qed.

Lemma insertion_sort_adjacent_head_forall :
  forall h l,
    (forall k, 0 <= k /\ k + 1 < Zlength (h :: l) ->
      Znth k (h :: l) 0 <= Znth (k + 1) (h :: l) 0) ->
    Forall (Z.le h) l.
Proof.
  intros h l.
  revert h.
  induction l; intros h Hadj.
  - constructor.
  - constructor.
    + specialize (Hadj 0).
      apply Hadj.
      rewrite !Zlength_cons.
      pose proof (Zlength_nonneg l).
      lia.
    + apply Forall_impl with (P := Z.le a).
      * intros x Hax.
        transitivity a; auto.
        specialize (Hadj 0).
        apply Hadj.
        rewrite !Zlength_cons.
        pose proof (Zlength_nonneg l).
        lia.
      * apply IHl.
        apply insertion_sort_adjacent_tail with (h := h).
        exact Hadj.
Qed.

Lemma insertion_sort_strong_sorted_from_adjacent :
  forall l,
    (forall k, 0 <= k /\ k + 1 < Zlength l ->
      Znth k l 0 <= Znth (k + 1) l 0) ->
    StronglySorted Z.le l.
Proof.
  induction l.
  - intros. constructor.
  - intros Hadj.
    constructor.
    + apply IHl.
      apply insertion_sort_adjacent_tail with (h := a).
      exact Hadj.
    + apply insertion_sort_adjacent_head_forall.
      exact Hadj.
Qed.

Lemma proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_length. Intros.
  Exists l_outer l_outer.
  entailer!.
  - replace (i - 1 + 2) with (i + 1) by lia.
    replace (i - 1 + 1) with i by lia.
    rewrite (sublist_nil l_outer i i) by lia.
    rewrite app_nil_l.
    replace n_pre with (Zlength l_outer) by lia.
    rewrite <- sublist_split with (lo := 0) (mid := i + 1) (hi := Zlength l_outer)
      by (try rewrite Zlength_correct; lia).
    rewrite insertion_sort_sublist_full_Zlength.
    reflexivity.
Qed. 

Lemma proof_of_insertion_sort_entail_wit_3 : insertion_sort_entail_wit_3.
Proof.
  pre_process.
  Exists (replace_Znth (j + 1) (Znth j l_cur_2 0) l_cur_2) l_base_2.
  entailer!.
  - replace (j - 1 + 2) with (j + 1) by lia.
    replace (j - 1 + 1) with j by lia.
    eapply insertion_sort_shift_list_eq
      with (n := n_pre) (j := j) (i := i_2)
           (l_base := l_base_2) (l_cur := l_cur_2);
      try lia; try exact H10.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite <- (insertion_sort_lcur_Znth_base n_pre j i_2 l_base_2 l_cur_2);
        try lia; try exact H10.
    + apply H9. lia.
Qed. 

Lemma proof_of_insertion_sort_entail_wit_4_1 : insertion_sort_entail_wit_4_1.
Proof.
  pre_process.
  Exists (replace_Znth (j + 1) key l_cur).
  entailer!.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    cancel.
  - eapply insertion_sort_final_adj_ge with
      (n := n_pre) (j := j) (i := i)
      (l_base := l_base) (l_cur := l_cur) (key := key);
      try lia; try eauto; try exact H10; try exact H5.
  - eapply Permutation_trans.
    + exact H7.
    + eapply insertion_sort_final_perm with
        (n := n_pre) (j := j) (i := i)
        (l_base := l_base) (l_cur := l_cur) (key := key);
        try lia; try eauto; try exact H10; try exact H5.
  - eapply insertion_sort_final_Zlength with
      (n := n_pre) (j := j) (i := i)
      (l_base := l_base) (l_cur := l_cur) (key := key);
      try lia; try eauto; try exact H10; try exact H5.
Qed. 

Lemma proof_of_insertion_sort_entail_wit_4_2 : insertion_sort_entail_wit_4_2.
Proof.
  pre_process.
  Exists (replace_Znth (j + 1) key l_cur).
  entailer!.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    cancel.
  - eapply insertion_sort_final_adj_neg with
      (n := n_pre) (j := j) (i := i)
      (l_base := l_base) (l_cur := l_cur) (key := key);
      try lia; try eauto; try exact H9; try exact H4.
  - eapply Permutation_trans.
    + exact H6.
    + eapply insertion_sort_final_perm with
        (n := n_pre) (j := j) (i := i)
        (l_base := l_base) (l_cur := l_cur) (key := key);
        try lia; try eauto; try exact H9; try exact H4.
  - eapply insertion_sort_final_Zlength with
      (n := n_pre) (j := j) (i := i)
      (l_base := l_base) (l_cur := l_cur) (key := key);
      try lia; try eauto; try exact H9; try exact H4.
Qed. 

Lemma proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Proof.
  pre_process.
  Exists l_outer.
  entailer!.
  unfold insertion_sort_spec.
  split.
  - destruct (Z_gt_dec n_pre 0) as [Hnpos | Hnle].
    + assert (i = n_pre) by lia.
      subst i.
      apply insertion_sort_strong_sorted_from_adjacent.
      intros k Hk.
      apply H5.
      rewrite H3 in Hk.
      exact Hk.
    + assert (n_pre = 0) by lia.
      assert (Hlen0 : Zlength l_outer = 0) by lia.
      subst n_pre.
      destruct l_outer.
      * constructor.
      * rewrite Zlength_cons in Hlen0.
        pose proof (Zlength_nonneg l_outer).
        lia.
  - exact H4.
Qed. 
