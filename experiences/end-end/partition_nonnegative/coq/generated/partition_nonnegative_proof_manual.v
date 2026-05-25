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
Require Import partition_nonnegative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma partition_nonnegative_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros T l.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl; reflexivity.
Qed.

Lemma partition_nonnegative_nth_replace_nth_eq:
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

Lemma partition_nonnegative_nth_replace_nth_other:
  forall T (l: list T) m n (v u: T),
    (m <> n)%nat ->
    nth m (replace_nth n v l) u = nth m l u.
Proof.
  intros T l.
  induction l; intros.
  - destruct m; destruct n; try lia; reflexivity.
  - destruct m; simpl.
    + destruct n; simpl; [lia | reflexivity].
    + destruct n; simpl; try reflexivity.
      assert (m <> n)%nat by lia.
      apply IHl; easy.
Qed.

Lemma partition_nonnegative_replace_Znth_length {A: Type}:
  forall (l:list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite partition_nonnegative_replace_nth_length.
  reflexivity.
Qed.

Lemma partition_nonnegative_Znth_replace_Znth_eq :
  forall {A} n (l : list A) v d,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply partition_nonnegative_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma partition_nonnegative_Znth_replace_Znth_other :
  forall {A} n m (l : list A) v d,
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply partition_nonnegative_nth_replace_nth_other.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Definition partition_nonnegative_swap (l : list Z) (i j : Z) : list Z :=
  replace_Znth j (Znth i l 0)
    (replace_Znth i (Znth j l 0) l).

Lemma partition_nonnegative_swap_length :
  forall l i j,
    Zlength (partition_nonnegative_swap l i j) = Zlength l.
Proof.
  intros.
  unfold partition_nonnegative_swap.
  rewrite !partition_nonnegative_replace_Znth_length.
  reflexivity.
Qed.

Lemma partition_nonnegative_swap_Znth_i :
  forall l i j,
    0 <= i /\ i <= j /\ j < Zlength l ->
    Znth i (partition_nonnegative_swap l i j) 0 = Znth j l 0.
Proof.
  intros l i j Hrange.
  unfold partition_nonnegative_swap.
  destruct (Z.eq_dec i j) as [Heq|Hneq].
  - subst j.
    rewrite partition_nonnegative_Znth_replace_Znth_eq.
    + reflexivity.
    + rewrite partition_nonnegative_replace_Znth_length. lia.
  - assert (Hi_inner :
      0 <= i < Zlength (replace_Znth i (Znth j l 0) l)).
    { rewrite partition_nonnegative_replace_Znth_length. lia. }
    rewrite partition_nonnegative_Znth_replace_Znth_other
      with (n := j) by (try exact Hi_inner; lia).
    apply partition_nonnegative_Znth_replace_Znth_eq.
    lia.
Qed.

Lemma partition_nonnegative_swap_Znth_j :
  forall l i j,
    0 <= i /\ i <= j /\ j < Zlength l ->
    Znth j (partition_nonnegative_swap l i j) 0 = Znth i l 0.
Proof.
  intros l i j Hrange.
  unfold partition_nonnegative_swap.
  apply partition_nonnegative_Znth_replace_Znth_eq.
  rewrite partition_nonnegative_replace_Znth_length.
  lia.
Qed.

Lemma partition_nonnegative_swap_Znth_other :
  forall l i j p,
    0 <= i /\ i <= j /\ j < Zlength l ->
    0 <= p < Zlength l ->
    p <> i ->
    p <> j ->
    Znth p (partition_nonnegative_swap l i j) 0 = Znth p l 0.
Proof.
  intros l i j p Hrange Hp Hpi Hpj.
  unfold partition_nonnegative_swap.
  assert (Hp_inner :
    0 <= p < Zlength (replace_Znth i (Znth j l 0) l)).
  { rewrite partition_nonnegative_replace_Znth_length. exact Hp. }
  rewrite partition_nonnegative_Znth_replace_Znth_other
    with (n := j) by (try exact Hp_inner; lia).
  apply partition_nonnegative_Znth_replace_Znth_other; lia.
Qed.

Lemma partition_nonnegative_swap_split_eq :
  forall pref mid tail x y,
    partition_nonnegative_swap
      (pref ++ x :: mid ++ y :: tail)
      (Zlength pref)
      (Zlength pref + 1 + Zlength mid) =
    pref ++ y :: mid ++ x :: tail.
Proof.
  intros.
  pose proof (Zlength_nonneg pref).
  pose proof (Zlength_nonneg mid).
  pose proof (Zlength_nonneg tail).
  apply (proj2 (list_eq_ext 0 _ _)).
  split.
  - rewrite partition_nonnegative_swap_length.
    repeat rewrite Zlength_app.
    repeat rewrite Zlength_cons.
    unfold Z.succ.
    repeat rewrite Zlength_app.
    repeat rewrite Zlength_cons.
    lia.
  - intros p Hp.
    rewrite partition_nonnegative_swap_length in Hp.
    assert (Hp_orig : 0 <= p < Zlength (pref ++ x :: mid ++ y :: tail)).
    { exact Hp. }
    rewrite !Zlength_app, !Zlength_cons in Hp.
    destruct (Z.eq_dec p (Zlength pref)) as [Hp_i|Hp_i].
    + subst p.
      rewrite partition_nonnegative_swap_Znth_i.
      * rewrite (@app_Znth2 Z pref (x :: mid ++ y :: tail)
          (Zlength pref + 1 + Zlength mid) 0) by lia.
        replace (Zlength pref + 1 + Zlength mid - Zlength pref)
          with (1 + Zlength mid) by lia.
        rewrite Znth_cons by lia.
        replace (1 + Zlength mid - 1) with (Zlength mid) by lia.
        rewrite (@app_Znth2 Z mid (y :: tail) (Zlength mid) 0) by lia.
        replace (Zlength mid - Zlength mid) with 0 by lia.
        rewrite (@app_Znth2 Z pref (y :: mid ++ x :: tail)
          (Zlength pref) 0) by lia.
        replace (Zlength pref - Zlength pref) with 0 by lia.
        apply Znth0_cons.
      * repeat rewrite Zlength_app.
        repeat rewrite Zlength_cons.
        unfold Z.succ.
        repeat rewrite Zlength_app.
        repeat rewrite Zlength_cons.
        lia.
    + destruct (Z.eq_dec p (Zlength pref + 1 + Zlength mid)) as [Hp_j|Hp_j].
      * subst p.
        rewrite partition_nonnegative_swap_Znth_j.
        -- rewrite (@app_Znth2 Z pref (x :: mid ++ y :: tail)
             (Zlength pref) 0) by lia.
           replace (Zlength pref - Zlength pref) with 0 by lia.
           rewrite Znth0_cons.
           rewrite (@app_Znth2 Z pref (y :: mid ++ x :: tail)
             (Zlength pref + 1 + Zlength mid) 0) by lia.
           replace (Zlength pref + 1 + Zlength mid - Zlength pref)
             with (1 + Zlength mid) by lia.
           rewrite Znth_cons by lia.
           replace (1 + Zlength mid - 1) with (Zlength mid) by lia.
           rewrite (@app_Znth2 Z mid (x :: tail) (Zlength mid) 0) by lia.
           replace (Zlength mid - Zlength mid) with 0 by lia.
           rewrite Znth0_cons.
           reflexivity.
        -- repeat rewrite Zlength_app.
           repeat rewrite Zlength_cons.
           unfold Z.succ.
           repeat rewrite Zlength_app.
           repeat rewrite Zlength_cons.
           lia.
      * rewrite partition_nonnegative_swap_Znth_other.
        -- destruct (Z_lt_ge_dec p (Zlength pref)) as [Hp_pref|Hp_pref].
           ++ rewrite (@app_Znth1 Z pref (x :: mid ++ y :: tail) p 0) by lia.
              rewrite (@app_Znth1 Z pref (y :: mid ++ x :: tail) p 0) by lia.
              reflexivity.
           ++ rewrite (@app_Znth2 Z pref (x :: mid ++ y :: tail) p 0) by lia.
              rewrite (@app_Znth2 Z pref (y :: mid ++ x :: tail) p 0) by lia.
              set (r := p - Zlength pref).
              assert (Hr_nonzero : r <> 0) by (unfold r; lia).
              assert (Hr_not_j : r <> 1 + Zlength mid) by (unfold r; lia).
              destruct (Z_lt_ge_dec r (1 + Zlength mid)) as [Hr_mid|Hr_tail].
              ** rewrite Znth_cons by lia.
                 rewrite Znth_cons by lia.
                 rewrite (@app_Znth1 Z mid (y :: tail) (r - 1) 0) by lia.
                 rewrite (@app_Znth1 Z mid (x :: tail) (r - 1) 0) by lia.
                 reflexivity.
              ** rewrite Znth_cons by lia.
                 rewrite Znth_cons by lia.
                 rewrite (@app_Znth2 Z mid (y :: tail) (r - 1) 0) by lia.
                 rewrite (@app_Znth2 Z mid (x :: tail) (r - 1) 0) by lia.
                 rewrite Znth_cons by lia.
                 rewrite Znth_cons by lia.
                 reflexivity.
        -- repeat rewrite Zlength_app.
           repeat rewrite Zlength_cons.
           unfold Z.succ.
           repeat rewrite Zlength_app.
           repeat rewrite Zlength_cons.
           lia.
        -- exact Hp_orig.
        -- lia.
        -- lia.
Qed.

Lemma partition_nonnegative_swap_perm :
  forall l i j,
    0 <= i /\ i <= j /\ j < Zlength l ->
    Permutation l (partition_nonnegative_swap l i j).
Proof.
  intros l i j Hrange.
  destruct (Z.eq_dec i j) as [Heq|Hneq].
  - subst j.
    unfold partition_nonnegative_swap.
    assert (Hsame :
      replace_Znth i (Znth i l 0) (replace_Znth i (Znth i l 0) l) = l).
    { apply (proj2 (list_eq_ext 0 _ _)).
      split.
      - rewrite !partition_nonnegative_replace_Znth_length. reflexivity.
      - intros p Hp.
        destruct (Z.eq_dec p i) as [Hpi|Hpi].
        + subst p.
          rewrite partition_nonnegative_Znth_replace_Znth_eq by
            (rewrite partition_nonnegative_replace_Znth_length; lia).
          reflexivity.
        + assert (Hp_inner :
            0 <= p < Zlength (replace_Znth i (Znth i l 0) l)).
          { rewrite !partition_nonnegative_replace_Znth_length in Hp.
            rewrite partition_nonnegative_replace_Znth_length.
            lia. }
          rewrite (@partition_nonnegative_Znth_replace_Znth_other Z i p
            (replace_Znth i (Znth i l 0) l) (Znth i l 0) 0)
            by (try exact Hp_inner; lia).
          assert (Hp_l : 0 <= p < Zlength l).
          { rewrite !partition_nonnegative_replace_Znth_length in Hp. exact Hp. }
          rewrite (@partition_nonnegative_Znth_replace_Znth_other Z i p l
            (Znth i l 0) 0) by (try exact Hp_l; lia).
          reflexivity. }
    rewrite Hsame.
    apply Permutation_refl.
  - assert (Hi_nat : (Z.to_nat i < length l)%nat).
    { rewrite Zlength_correct in Hrange. lia. }
    rewrite (list_split_nth _ (Z.to_nat i) l 0 Hi_nat).
    set (pref := firstn (Z.to_nat i) l).
    set (rest := skipn (S (Z.to_nat i)) l).
    assert (Hpref_len : Zlength pref = i).
    { unfold pref. rewrite Zlength_correct, firstn_length. lia. }
    assert (Hj_rest : (Z.to_nat (j - i - 1) < length rest)%nat).
    { unfold rest. rewrite skipn_length. rewrite Zlength_correct in Hrange. lia. }
    rewrite (list_split_nth _ (Z.to_nat (j - i - 1)) rest 0 Hj_rest).
    set (mid := firstn (Z.to_nat (j - i - 1)) rest).
    set (tail := skipn (S (Z.to_nat (j - i - 1))) rest).
    assert (Hmid_len : Zlength mid = j - i - 1).
    { unfold mid. rewrite Zlength_correct, firstn_length. lia. }
    set (x0 := nth (Z.to_nat i) l 0).
    set (y0 := nth (Z.to_nat (j - i - 1)) rest 0).
    change (Permutation (pref ++ x0 :: mid ++ y0 :: tail)
      (partition_nonnegative_swap (pref ++ x0 :: mid ++ y0 :: tail) i j)).
    replace i with (Zlength pref) by lia.
    replace j with (Zlength pref + 1 + Zlength mid) by lia.
    rewrite partition_nonnegative_swap_split_eq.
    apply Permutation_trans with
      (l' := pref ++ y0 :: mid ++ x0 :: tail).
    { apply Permutation_app_head.
      apply Permutation_trans with
        (l' := mid ++ x0 :: y0 :: tail).
      + apply Permutation_middle.
      + apply Permutation_trans with
          (l' := mid ++ y0 :: x0 :: tail).
        * apply Permutation_app_head. apply perm_swap.
        * symmetry. apply Permutation_middle. }
    { apply Permutation_refl. }
Qed.

Lemma proof_of_partition_nonnegative_entail_wit_1 : partition_nonnegative_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_partition_nonnegative_entail_wit_2_1 : partition_nonnegative_entail_wit_2_1.
Proof.
  pre_process.
  Exists (partition_nonnegative_swap lc_2 i j).
  Intros.
  prop_apply IntArray.full_length.
  entailer!; try lia.
  - unfold partition_nonnegative_swap.
    sep_apply store_int_undef_store_int.
    entailer!.
  - eapply Permutation_trans.
    + exact H9.
    + apply partition_nonnegative_swap_perm.
      rewrite H6. lia.
  - intros q Hq.
    destruct (Z.eq_dec q j) as [Hqj|Hqj].
    + subst q.
      rewrite partition_nonnegative_swap_Znth_j.
      * exact H.
      * rewrite H6. lia.
    + rewrite partition_nonnegative_swap_Znth_other.
      * apply H8. lia.
      * rewrite H6. lia.
      * rewrite H6. lia.
      * lia.
      * lia.
  - intros p Hp.
    rewrite partition_nonnegative_swap_Znth_other.
    + apply H7. lia.
    + rewrite H6. lia.
    + rewrite H6. lia.
    + lia.
    + lia.
  - rewrite partition_nonnegative_swap_length.
    exact H6.
Qed. 
