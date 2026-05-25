Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
From AUXLib Require Import ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import bubble_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma bubble_sort_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros T l.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl; reflexivity.
Qed.

Lemma bubble_sort_nth_replace_nth_eq:
  forall T (l: list T) i v u,
    (i < length l)%nat ->
    nth i (replace_nth i v l) u = v.
Proof.
  intros T l.
  induction l; intros; simpl in *.
  - lia.
  - destruct i; simpl.
    + reflexivity.
    + apply IHl; lia.
Qed.

Lemma bubble_sort_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros T l idx repl v u Hneq.
  revert idx repl Hneq.
  induction l; intros idx repl Hneq.
  - destruct idx; destruct repl; try lia; reflexivity.
  - destruct idx; destruct repl; simpl; try reflexivity; try lia.
    apply IHl; lia.
Qed.

Lemma bubble_sort_replace_Znth_length {A: Type}:
  forall (l:list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite bubble_sort_replace_nth_length.
  reflexivity.
Qed.

Lemma bubble_sort_Znth_replace_Znth_eq :
  forall {A} n (l : list A) v d,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply bubble_sort_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma bubble_sort_Znth_replace_Znth_other :
  forall {A} n m (l : list A) v d,
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply bubble_sort_nth_replace_nth_other.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Definition bubble_sort_adjacent_swap (l : list Z) (j : Z) : list Z :=
  replace_Znth (j + 1) (Znth j l 0)
    (replace_Znth j (Znth (j + 1) l 0) l).

Lemma bubble_sort_adjacent_swap_length :
  forall l j,
    Zlength (bubble_sort_adjacent_swap l j) = Zlength l.
Proof.
  intros.
  unfold bubble_sort_adjacent_swap.
  rewrite !bubble_sort_replace_Znth_length.
  reflexivity.
Qed.

Lemma bubble_sort_adjacent_swap_Znth_j :
  forall l j,
    0 <= j /\ j + 1 < Zlength l ->
    Znth j (bubble_sort_adjacent_swap l j) 0 = Znth (j + 1) l 0.
Proof.
  intros l j Hrange.
  unfold bubble_sort_adjacent_swap.
  rewrite (@bubble_sort_Znth_replace_Znth_other Z (j + 1) j
    (replace_Znth j (Znth (j + 1) l 0) l) (Znth j l 0) 0).
  - apply bubble_sort_Znth_replace_Znth_eq; lia.
  - lia.
  - rewrite bubble_sort_replace_Znth_length; lia.
  - lia.
Qed.

Lemma bubble_sort_adjacent_swap_Znth_j1 :
  forall l j,
    0 <= j /\ j + 1 < Zlength l ->
    Znth (j + 1) (bubble_sort_adjacent_swap l j) 0 = Znth j l 0.
Proof.
  intros l j Hrange.
  unfold bubble_sort_adjacent_swap.
  apply bubble_sort_Znth_replace_Znth_eq.
  rewrite bubble_sort_replace_Znth_length.
  lia.
Qed.

Lemma bubble_sort_adjacent_swap_Znth_other :
  forall l j p,
    0 <= j /\ j + 1 < Zlength l ->
    0 <= p < Zlength l ->
    p <> j ->
    p <> j + 1 ->
    Znth p (bubble_sort_adjacent_swap l j) 0 = Znth p l 0.
Proof.
  intros l j p Hrange Hp Hpj Hpj1.
  unfold bubble_sort_adjacent_swap.
  rewrite (@bubble_sort_Znth_replace_Znth_other Z (j + 1) p
    (replace_Znth j (Znth (j + 1) l 0) l) (Znth j l 0) 0).
  - apply bubble_sort_Znth_replace_Znth_other; lia.
  - lia.
  - rewrite bubble_sort_replace_Znth_length; lia.
  - lia.
Qed.

Lemma bubble_sort_replace_nth_at_app :
  forall (pref tail : list Z) x y,
    replace_nth (length pref) y (pref ++ x :: tail) =
    pref ++ y :: tail.
Proof.
  induction pref; intros; simpl.
  - reflexivity.
  - rewrite IHpref. reflexivity.
Qed.

Lemma bubble_sort_replace_nth_succ_at_app :
  forall (pref tail : list Z) x y z,
    replace_nth (S (length pref)) z (pref ++ x :: y :: tail) =
    pref ++ x :: z :: tail.
Proof.
  intros.
  replace (S (length pref)) with (length (pref ++ x :: nil)).
  2:{ rewrite app_length; simpl; lia. }
  replace (pref ++ x :: y :: tail) with ((pref ++ x :: nil) ++ y :: tail).
  2:{ rewrite <- app_assoc. reflexivity. }
  rewrite bubble_sort_replace_nth_at_app.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma bubble_sort_adjacent_swap_split_eq :
  forall (pref tail : list Z) x y,
    bubble_sort_adjacent_swap (pref ++ x :: y :: tail) (Zlength pref) =
    pref ++ y :: x :: tail.
Proof.
  intros.
  unfold bubble_sort_adjacent_swap.
  assert (Hx : Znth (Zlength pref) (pref ++ x :: y :: tail) 0 = x).
  { rewrite app_Znth2 by lia.
    replace (Zlength pref - Zlength pref) with 0 by lia.
    apply Znth0_cons. }
  assert (Hy : Znth (Zlength pref + 1) (pref ++ x :: y :: tail) 0 = y).
  { rewrite app_Znth2 by lia.
    replace (Zlength pref + 1 - Zlength pref) with 1 by lia.
    rewrite Znth_cons by lia.
    replace (1 - 1) with 0 by lia.
    apply Znth0_cons. }
  rewrite Hx, Hy.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length pref))) with (length pref) by lia.
  replace (Z.to_nat (Z.of_nat (length pref) + 1)) with (S (length pref)) by lia.
  rewrite bubble_sort_replace_nth_at_app.
  rewrite bubble_sort_replace_nth_succ_at_app.
  reflexivity.
Qed.

Lemma bubble_sort_adjacent_swap_perm :
  forall l j,
    0 <= j /\ j + 1 < Zlength l ->
    Permutation l (bubble_sort_adjacent_swap l j).
Proof.
  intros l j Hrange.
  assert (Hj_nat : (Z.to_nat j < length l)%nat).
  { rewrite Zlength_correct in Hrange. lia. }
  rewrite (list_split_nth _ (Z.to_nat j) l 0 Hj_nat).
  set (pref := firstn (Z.to_nat j) l).
  assert (Hpref_len : Zlength pref = j).
  { unfold pref. rewrite Zlength_correct, firstn_length. lia. }
  assert (Hj1_nat :
    (0 < length (skipn (S (Z.to_nat j)) l))%nat).
  { rewrite skipn_length. rewrite Zlength_correct in Hrange. lia. }
  rewrite (list_split_nth _ 0 (skipn (S (Z.to_nat j)) l) 0 Hj1_nat).
  set (x0 := nth (Z.to_nat j) l 0).
  set (y0 := nth 0 (skipn (S (Z.to_nat j)) l) 0).
  set (tail := skipn (S 0) (skipn (S (Z.to_nat j)) l)).
  change (Permutation (pref ++ x0 :: y0 :: tail)
    (bubble_sort_adjacent_swap (pref ++ x0 :: y0 :: tail) j)).
  replace j with (Zlength pref) by lia.
  rewrite bubble_sort_adjacent_swap_split_eq.
  apply Permutation_app_head.
  apply perm_swap.
Qed.

Lemma bubble_sort_adjacent_swap_suffix_order :
  forall l j bound p q,
    0 <= j /\ j + 1 < bound /\ bound <= Zlength l ->
    bound <= p /\ p <= q /\ q < Zlength l ->
    (forall p q, bound <= p /\ p <= q /\ q < Zlength l -> Znth p l 0 <= Znth q l 0) ->
    Znth p (bubble_sort_adjacent_swap l j) 0 <=
    Znth q (bubble_sort_adjacent_swap l j) 0.
Proof.
  intros l j bound p q Hrange Hpq Hsuf.
  rewrite bubble_sort_adjacent_swap_Znth_other by lia.
  rewrite bubble_sort_adjacent_swap_Znth_other by lia.
  apply Hsuf; lia.
Qed.

Lemma bubble_sort_adjacent_swap_cross_order :
  forall l j bound p q,
    0 <= j /\ j + 1 < bound /\ bound <= Zlength l ->
    0 <= p /\ p < bound /\ bound <= q /\ q < Zlength l ->
    (forall p q, 0 <= p /\ p < bound /\ bound <= q /\ q < Zlength l -> Znth p l 0 <= Znth q l 0) ->
    Znth p (bubble_sort_adjacent_swap l j) 0 <=
    Znth q (bubble_sort_adjacent_swap l j) 0.
Proof.
  intros l j bound p q Hrange Hpq Hcross.
  rewrite bubble_sort_adjacent_swap_Znth_other with (p := q) by lia.
  destruct (Z.eq_dec p j) as [Hpj|Hpj].
  - subst p.
    rewrite bubble_sort_adjacent_swap_Znth_j by lia.
    apply Hcross; lia.
  - destruct (Z.eq_dec p (j + 1)) as [Hpj1|Hpj1].
    + subst p.
      rewrite bubble_sort_adjacent_swap_Znth_j1 by lia.
      apply Hcross; lia.
    + rewrite bubble_sort_adjacent_swap_Znth_other by lia.
      apply Hcross; lia.
Qed.

Lemma bubble_sort_adjacent_swap_local_max :
  forall l j p,
    0 <= j /\ j + 1 < Zlength l ->
    Znth j l 0 > Znth (j + 1) l 0 ->
    (forall p, 0 <= p /\ p < j -> Znth p l 0 <= Znth j l 0) ->
    0 <= p /\ p < j + 1 ->
    Znth p (bubble_sort_adjacent_swap l j) 0 <=
    Znth (j + 1) (bubble_sort_adjacent_swap l j) 0.
Proof.
  intros l j p Hrange Hgt Hmax Hp.
  rewrite bubble_sort_adjacent_swap_Znth_j1 by lia.
  destruct (Z.eq_dec p j) as [Hpj|Hpj].
  - subst p.
    rewrite bubble_sort_adjacent_swap_Znth_j by lia.
    lia.
  - rewrite bubble_sort_adjacent_swap_Znth_other by lia.
    apply Hmax; lia.
Qed.

Lemma bubble_sort_outer_suffix_extend :
  forall l i j n p q,
    j + 1 >= n - i ->
    0 <= j ->
    j + 1 <= n - i ->
    0 <= i ->
    i < n ->
    Zlength l = n ->
    (forall p q, n - i <= p /\ p <= q /\ q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall p q, 0 <= p /\ p < n - i /\ n - i <= q /\ q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall p, 0 <= p /\ p < j -> Znth p l 0 <= Znth j l 0) ->
    n - (i + 1) <= p /\ p <= q /\ q < n ->
    Znth p l 0 <= Znth q l 0.
Proof.
  intros l i j n p q Hexit Hj0 Hjle Hi0 Hin Hlen Hsuf Hcross Hmax Hpq.
  assert (Hj : j = n - i - 1) by lia.
  subst j.
  destruct (Z.eq_dec p (n - i - 1)) as [Hpfirst|Hpfirst].
  - subst p.
    destruct (Z.eq_dec q (n - i - 1)) as [Hqfirst|Hqfirst].
    + subst q. lia.
    + apply Hcross; lia.
  - destruct (Z_lt_ge_dec p (n - i)) as [Hplt|Hpge].
    + assert (p < n - i - 1) by lia.
      transitivity (Znth (n - i - 1) l 0).
      * apply Hmax; lia.
      * destruct (Z.eq_dec q (n - i - 1)) as [Hqfirst|Hqfirst].
        -- subst q. lia.
        -- apply Hcross; lia.
    + apply Hsuf; lia.
Qed.

Lemma bubble_sort_outer_cross_extend :
  forall l i j n p q,
    j + 1 >= n - i ->
    0 <= j ->
    j + 1 <= n - i ->
    0 <= i ->
    i < n ->
    Zlength l = n ->
    (forall p q, n - i <= p /\ p <= q /\ q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall p q, 0 <= p /\ p < n - i /\ n - i <= q /\ q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall p, 0 <= p /\ p < j -> Znth p l 0 <= Znth j l 0) ->
    0 <= p /\ p < n - (i + 1) /\ n - (i + 1) <= q /\ q < n ->
    Znth p l 0 <= Znth q l 0.
Proof.
  intros l i j n p q Hexit Hj0 Hjle Hi0 Hin Hlen Hsuf Hcross Hmax Hpq.
  assert (Hj : j = n - i - 1) by lia.
  subst j.
  destruct (Z.eq_dec q (n - i - 1)) as [Hqfirst|Hqfirst].
  - subst q.
    apply Hmax; lia.
  - destruct (Z_lt_ge_dec q (n - i)) as [Hqlt|Hqge].
    + lia.
    + apply Hcross; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Proof.
  pre_process.
  Exists lc.
  entailer!.
Qed. 

Lemma proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Proof.
  unfold bubble_sort_entail_wit_3_1.
  intros.
  Exists (bubble_sort_adjacent_swap lc_3 j).
  Intros.
  prop_apply IntArray.full_length.
  entailer!; try lia.
  all: try solve [rewrite bubble_sort_adjacent_swap_length; lia].
  all: try solve [
    eapply Permutation_trans;
    [ eassumption | apply bubble_sort_adjacent_swap_perm; lia ]].
  all: try solve [
    intros p q Hpq;
    change (Znth p (bubble_sort_adjacent_swap lc_3 j) 0 <=
      Znth q (bubble_sort_adjacent_swap lc_3 j) 0);
    eapply bubble_sort_adjacent_swap_suffix_order with (bound := n_pre - i_2);
    try lia;
    intros p' q' Hp'q';
    apply H8; lia ].
  all: try solve [
    intros p q Hpq;
    change (Znth p (bubble_sort_adjacent_swap lc_3 j) 0 <=
      Znth q (bubble_sort_adjacent_swap lc_3 j) 0);
    eapply bubble_sort_adjacent_swap_cross_order with (bound := n_pre - i_2);
    try lia;
    intros p' q' Hp'q';
    apply H9; lia ].
  all: try solve [
    intros p Hp;
    change (Znth p (bubble_sort_adjacent_swap lc_3 j) 0 <=
      Znth (j + 1) (bubble_sort_adjacent_swap lc_3 j) 0);
    eapply bubble_sort_adjacent_swap_local_max; try lia;
    intros p' Hp';
    apply H10; lia ].
  eapply Permutation_trans.
  - exact H7.
  - apply bubble_sort_adjacent_swap_perm. lia.
Qed. 

Lemma proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Proof.
  unfold bubble_sort_entail_wit_4.
  intros.
  Exists lc_3.
  Intros.
  entailer!; try lia.
  all: try solve [eassumption].
  all: try solve [entailer!].
  - sep_apply store_int_undef_store_int.
    entailer!.
  - intros p q Hpq.
    eapply bubble_sort_outer_cross_extend; try eassumption; try lia.
    + intros p' q' Hp'q'. apply H7; lia.
    + intros p' q' Hp'q'. apply H8; lia.
  - intros p q Hpq.
    eapply bubble_sort_outer_suffix_extend; try eassumption; try lia.
    + intros p' q' Hp'q'. apply H7; lia.
    + intros p' q' Hp'q'. apply H8; lia.
Qed. 

Lemma proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Proof.
  pre_process.
  Exists lc.
  entailer!.
  intros i j Hij.
  replace i_2 with n_pre in H5 by lia.
  apply H5.
  lia.
Qed. 
