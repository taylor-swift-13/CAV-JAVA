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
From SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays Require Import merge_sorted_arrays_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import merge_sorted_arrays.
Import ListNotations.

Lemma replace_Znth_app_suffix_head_Z :
  forall (prefix lo : list Z) k n x,
    Zlength prefix = k ->
    0 <= k < n ->
    n <= Zlength lo ->
    replace_Znth k x (prefix ++ sublist k n lo) =
    (prefix ++ [x]) ++ sublist (k + 1) n lo.
Proof.
  intros prefix lo k n x Hlen Hk Hn.
  rewrite replace_Znth_app_r.
  2: lia.
  rewrite replace_Znth_nothing by lia.
  replace (k - Zlength prefix) with 0 by lia.
  assert (Hn_len: n <= Z.of_nat (length lo)).
  { rewrite <- Zlength_correct. exact Hn. }
  assert (Hsplit: sublist k n lo = sublist k (k + 1) lo ++ sublist (k + 1) n lo).
  { apply sublist_split; lia. }
  rewrite Hsplit.
  rewrite sublist_single with (a := x) by lia.
  unfold replace_Znth; simpl.
  replace ((prefix ++ [x]) ++ sublist (k + 1) n lo)
    with (prefix ++ x :: sublist (k + 1) n lo).
  - reflexivity.
  - rewrite <- app_assoc. reflexivity.
Qed.

Lemma merge_one_last :
  forall b x,
    Forall (fun z => z < x) b ->
    merge_sorted_arrays_spec [x] b = b ++ [x].
Proof.
  induction b; intros x Hb.
  - reflexivity.
  - inversion Hb; subst.
    simpl.
    destruct (Z.leb_spec x a); try lia.
    f_equal. apply IHb. assumption.
Qed.

Lemma merge_app_a_last :
  forall a b x,
    Forall (fun z => z <= x) a ->
    Forall (fun z => z < x) b ->
    merge_sorted_arrays_spec (a ++ [x]) b =
    merge_sorted_arrays_spec a b ++ [x].
Proof.
  induction a; intros b x Ha Hb.
  - simpl. apply merge_one_last. assumption.
  - rename a into z. rename a0 into zs.
    revert x z zs IHa Ha Hb.
    induction b; intros x z zs IHa Ha Hb.
    + reflexivity.
    + rename a into y. rename b into ys.
      inversion Ha; subst. inversion Hb; subst.
      simpl.
      destruct (Z.leb_spec z y).
      * simpl. f_equal. apply IHa; assumption.
      * simpl. f_equal. apply IHb; assumption.
Qed.

Lemma merge_right_one_last :
  forall a y,
    Forall (fun z => z <= y) a ->
    merge_sorted_arrays_spec a [y] = a ++ [y].
Proof.
  induction a; intros y Ha.
  - reflexivity.
  - inversion Ha; subst.
    simpl.
    destruct (Z.leb_spec a y); try lia.
    simpl. f_equal. apply IHa. assumption.
Qed.

Lemma merge_app_b_last :
  forall a b y,
    Forall (fun z => z <= y) a ->
    Forall (fun z => z <= y) b ->
    merge_sorted_arrays_spec a (b ++ [y]) =
    merge_sorted_arrays_spec a b ++ [y].
Proof.
  induction a; intros b y Ha Hb.
  - reflexivity.
  - rename a into x. rename a0 into xs.
    revert y x xs IHa Ha Hb.
    induction b; intros y x xs IHa Ha Hb.
    + inversion Ha; subst.
      simpl.
      destruct (Z.leb_spec x y); try lia.
      simpl. f_equal. apply merge_right_one_last. assumption.
    + rename a into z. rename b into zs.
      inversion Ha; subst. inversion Hb; subst.
      simpl.
      destruct (Z.leb_spec x z).
      * simpl. f_equal. apply (IHa (z :: zs) y); assumption.
      * simpl. f_equal. apply (IHb y x xs IHa); assumption.
Qed.

Lemma sublist_prefix_snoc_Z :
  forall (l : list Z) i x,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l x].
Proof.
  intros l i x Hi.
  assert (Hlen: i + 1 <= Z.of_nat (length l)).
  { rewrite <- Zlength_correct. lia. }
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite sublist_single with (a := x) by lia.
  reflexivity.
Qed.

Lemma Forall_sublist0_Znth_le_value :
  forall (l : list Z) i x,
    0 <= i <= Zlength l ->
    (forall p, 0 <= p < i -> Znth p l 0 <= x) ->
    Forall (fun z => z <= x) (sublist 0 i l).
Proof.
  induction l; intros i x Hrange Hprop.
  - rewrite sublist_of_nil. constructor.
  - destruct (Z_le_gt_dec i 0).
    + rewrite sublist_nil by lia. constructor.
    + rewrite sublist_cons1 by lia.
      constructor.
      * rewrite <- (Znth0_cons a l 0). apply Hprop. lia.
      * apply IHl.
        -- rewrite Zlength_cons in Hrange. lia.
        -- intros p Hp.
           specialize (Hprop (p + 1)).
           rewrite Znth_cons in Hprop by lia.
           replace (p + 1 - 1) with p in Hprop by lia.
           apply Hprop. lia.
Qed.

Lemma Forall_sublist0_Znth_lt_value :
  forall (l : list Z) i x,
    0 <= i <= Zlength l ->
    (forall p, 0 <= p < i -> Znth p l 0 < x) ->
    Forall (fun z => z < x) (sublist 0 i l).
Proof.
  induction l; intros i x Hrange Hprop.
  - rewrite sublist_of_nil. constructor.
  - destruct (Z_le_gt_dec i 0).
    + rewrite sublist_nil by lia. constructor.
    + rewrite sublist_cons1 by lia.
      constructor.
      * rewrite <- (Znth0_cons a l 0). apply Hprop. lia.
      * apply IHl.
        -- rewrite Zlength_cons in Hrange. lia.
        -- intros p Hp.
           specialize (Hprop (p + 1)).
           rewrite Znth_cons in Hprop by lia.
           replace (p + 1 - 1) with p in Hprop by lia.
           apply Hprop. lia.
Qed.

Lemma Zlength_merge_sorted_arrays_spec :
  forall a b,
    Zlength (merge_sorted_arrays_spec a b) = Zlength a + Zlength b.
Proof.
  induction a; intros b.
  - reflexivity.
  - rename a into x. rename a0 into xs.
    revert x xs IHa.
    induction b; intros x xs IHa.
    + simpl. rewrite Zlength_nil. lia.
    + rename a into y. rename b into ys.
      simpl.
      destruct (Z.leb_spec x y).
      * rewrite !Zlength_cons. rewrite IHa. rewrite !Zlength_cons. unfold Z.succ. lia.
      * change (Zlength (y :: merge_sorted_arrays_spec (x :: xs) ys) =
          Zlength (x :: xs) + Zlength (y :: ys)).
        rewrite !Zlength_cons. rewrite IHb by exact IHa. rewrite !Zlength_cons. unfold Z.succ. lia.
Qed.

Local Open Scope sac.

Lemma proof_of_merge_sorted_arrays_entail_wit_1 : merge_sorted_arrays_entail_wit_1.
Proof.
  pre_process.
  Exists nil.
  replace (sublist 0 (n_pre + m_pre) lo) with lo.
  - entailer!.
  - symmetry. apply sublist_self. symmetry. exact H4.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_2_1 : merge_sorted_arrays_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hla_snoc:
    sublist 0 (i_3 + 1) la = sublist 0 i_3 la ++ [Znth i_3 la 0]).
  {
    apply sublist_prefix_snoc_Z.
    rewrite H10. lia.
  }
  assert (Hforalla:
    Forall (fun z => z <= Znth i_3 la 0) (sublist 0 i_3 la)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H10. lia.
    - intros p Hp.
      apply H13. lia.
  }
  assert (Hforallb:
    Forall (fun z => z < Znth i_3 la 0) (sublist 0 j_3 lb)).
  {
    apply Forall_sublist0_Znth_lt_value.
    - rewrite H11. lia.
    - intros p Hp.
      apply H15 with (ai_2 := i_3). lia.
  }
  rewrite (replace_Znth_app_suffix_head_Z
    lout_done_2 lo k (n_pre + m_pre) (Znth i_3 la 0)).
  2: exact H17.
  2: lia.
  2: rewrite H12; lia.
  Exists (lout_done_2 ++ [Znth i_3 la 0]).
  entailer!.
  - rewrite Hla_snoc.
    rewrite merge_app_a_last.
    + rewrite <- H18. reflexivity.
    + exact Hforalla.
    + exact Hforallb.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros ap bi_2 Hap.
    destruct (Z_lt_ge_dec ap i_3).
    + apply H16. lia.
    + assert (ap = i_3) by lia. subst ap.
      assert (Znth i_3 la 0 <= Znth j_3 lb 0) by exact H.
      assert (Znth j_3 lb 0 <= Znth bi_2 lb 0).
      {
        apply H14. lia.
      }
      lia.
  - intros bp ai_2 Hbp.
    apply H15 with (ai_2 := ai_2). lia.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_2_2 : merge_sorted_arrays_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hlb_snoc:
    sublist 0 (j_3 + 1) lb = sublist 0 j_3 lb ++ [Znth j_3 lb 0]).
  {
    apply sublist_prefix_snoc_Z.
    rewrite H11. lia.
  }
  assert (Hforalla:
    Forall (fun z => z <= Znth j_3 lb 0) (sublist 0 i_3 la)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H10. lia.
    - intros p Hp.
      apply H16 with (bi_2 := j_3). lia.
  }
  assert (Hforallb:
    Forall (fun z => z <= Znth j_3 lb 0) (sublist 0 j_3 lb)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H11. lia.
    - intros p Hp.
      apply H14. lia.
  }
  rewrite (replace_Znth_app_suffix_head_Z
    lout_done_2 lo k (n_pre + m_pre) (Znth j_3 lb 0)).
  2: exact H17.
  2: lia.
  2: rewrite H12; lia.
  Exists (lout_done_2 ++ [Znth j_3 lb 0]).
  entailer!.
  - rewrite Hlb_snoc.
    rewrite merge_app_b_last.
    + rewrite <- H18. reflexivity.
    + exact Hforalla.
    + exact Hforallb.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros ap bi_2 Hap.
    apply H16 with (bi_2 := bi_2). lia.
  - intros bp ai_2 Hbp.
    destruct (Z_lt_ge_dec bp j_3).
    + apply H15 with (ai_2 := ai_2). lia.
    + assert (bp = j_3) by lia. subst bp.
      assert (Znth j_3 lb 0 < Znth i_3 la 0) by lia.
      assert (Znth i_3 la 0 <= Znth ai_2 la 0).
      {
        apply H13. lia.
      }
      lia.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_3_1 : merge_sorted_arrays_entail_wit_3_1.
Proof.
  pre_process.
  assert (j = m_pre) by lia.
  subst j.
  Right.
  Exists lout_done_2.
  entailer!.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_3_2 : merge_sorted_arrays_entail_wit_3_2.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  Left.
  Exists lout_done_2.
  entailer!.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_4 : merge_sorted_arrays_entail_wit_4.
Proof.
  pre_process.
  assert (Hla_snoc:
    sublist 0 (i + 1) la = sublist 0 i la ++ [Znth i la 0]).
  {
    apply sublist_prefix_snoc_Z.
    rewrite H9. lia.
  }
  assert (Hforalla:
    Forall (fun z => z <= Znth i la 0) (sublist 0 i la)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H9. lia.
    - intros p Hp.
      apply H12. lia.
  }
  assert (Hforallb:
    Forall (fun z => z < Znth i la 0) (sublist 0 j lb)).
  {
    apply Forall_sublist0_Znth_lt_value.
    - rewrite H10. lia.
    - intros p Hp.
      apply H14 with (ai_2 := i). lia.
  }
  rewrite (replace_Znth_app_suffix_head_Z
    lout_done_2 lo k (n_pre + m_pre) (Znth i la 0)).
  2: exact H16.
  2: lia.
  2: rewrite H11; lia.
  Right.
  Exists (lout_done_2 ++ [Znth i la 0]).
  entailer!.
  - rewrite Hla_snoc.
    rewrite merge_app_a_last.
    + rewrite <- H17. reflexivity.
    + exact Hforalla.
    + exact Hforallb.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros bp ai_2 Hbp.
    apply H14 with (ai_2 := ai_2). lia.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_5_1 : merge_sorted_arrays_entail_wit_5_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  Exists lout_done_2.
  entailer!.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_5_2 : merge_sorted_arrays_entail_wit_5_2.
Proof.
  pre_process.
  Exists lout_done_2.
  entailer!.
Qed.

Lemma proof_of_merge_sorted_arrays_entail_wit_6 : merge_sorted_arrays_entail_wit_6.
Proof.
  pre_process.
  assert (Hn_nonneg: 0 <= n_pre).
  {
    rewrite <- H7.
    apply Zlength_nonneg.
  }
  assert (Hlb_snoc:
    sublist 0 (j + 1) lb = sublist 0 j lb ++ [Znth j lb 0]).
  {
    apply sublist_prefix_snoc_Z.
    rewrite H8. lia.
  }
  assert (Hforalla:
    Forall (fun z => z <= Znth j lb 0) (sublist 0 i la)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H7. lia.
    - intros p Hp.
      apply H13 with (bi_2 := j). lia.
  }
  assert (Hforallb:
    Forall (fun z => z <= Znth j lb 0) (sublist 0 j lb)).
  {
    apply Forall_sublist0_Znth_le_value.
    - rewrite H8. lia.
    - intros p Hp.
      apply H11. lia.
  }
  rewrite (replace_Znth_app_suffix_head_Z
    lout_done_2 lo k (n_pre + m_pre) (Znth j lb 0)).
  2: exact H14.
  2: lia.
  2: rewrite H9; lia.
  Exists (lout_done_2 ++ [Znth j lb 0]).
  entailer!.
  - rewrite Hlb_snoc.
    rewrite merge_app_b_last.
    + rewrite <- H15. reflexivity.
    + exact Hforalla.
    + exact Hforallb.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros bp ai_2 Hbp.
    apply H13 with (bi_2 := ai_2). lia.
Qed.

Lemma proof_of_merge_sorted_arrays_return_wit_1 : merge_sorted_arrays_return_wit_1.
Proof.
  pre_process.
  assert (j = m_pre) by lia.
  subst j.
  subst i.
  assert (k = n_pre + m_pre) by lia.
  subst k.
  assert (Hla_full: sublist 0 n_pre la = la).
  {
    apply sublist_self.
    rewrite H7. lia.
  }
  assert (Hlb_full: sublist 0 m_pre lb = lb).
  {
    apply sublist_self.
    rewrite H8. lia.
  }
  rewrite sublist_nil by lia.
  rewrite app_nil_r.
  rewrite Hla_full in H15.
  rewrite Hlb_full in H15.
  subst lout_done.
  entailer!.
Qed.
