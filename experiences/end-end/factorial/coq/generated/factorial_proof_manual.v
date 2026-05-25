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
From SimpleC.EE.CAV.verify_20260422_161944_factorial Require Import factorial_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_fac_safety_wit_3 : fac_safety_wit_3.
Proof.
  unfold fac_safety_wit_3.
  intros.
  Intros.
  entailer!.
  - assert (1 <= i <= 10) as Hi_range by lia.
    destruct (Z.eq_dec i 1) as [Hi_eq_1 | Hi_neq_1].
    + rewrite Hi_eq_1. vm_compute. congruence.
    + destruct (Z.eq_dec i 2) as [Hi_eq_2 | Hi_neq_2].
      * rewrite Hi_eq_2. vm_compute. congruence.
      * destruct (Z.eq_dec i 3) as [Hi_eq_3 | Hi_neq_3].
        { rewrite Hi_eq_3. vm_compute. congruence. }
        destruct (Z.eq_dec i 4) as [Hi_eq_4 | Hi_neq_4].
        { rewrite Hi_eq_4. vm_compute. congruence. }
        destruct (Z.eq_dec i 5) as [Hi_eq_5 | Hi_neq_5].
        { rewrite Hi_eq_5. vm_compute. congruence. }
        destruct (Z.eq_dec i 6) as [Hi_eq_6 | Hi_neq_6].
        { rewrite Hi_eq_6. vm_compute. congruence. }
        destruct (Z.eq_dec i 7) as [Hi_eq_7 | Hi_neq_7].
        { rewrite Hi_eq_7. vm_compute. congruence. }
        destruct (Z.eq_dec i 8) as [Hi_eq_8 | Hi_neq_8].
        { rewrite Hi_eq_8. vm_compute. congruence. }
        destruct (Z.eq_dec i 9) as [Hi_eq_9 | Hi_neq_9].
        { rewrite Hi_eq_9. vm_compute. congruence. }
        assert (i = 10) by lia.
        subst i.
        vm_compute. congruence.
  - assert (1 <= i <= 10) as Hi_range by lia.
    destruct (Z.eq_dec i 1) as [Hi_eq_1 | Hi_neq_1].
    + rewrite Hi_eq_1. vm_compute. congruence.
    + destruct (Z.eq_dec i 2) as [Hi_eq_2 | Hi_neq_2].
      * rewrite Hi_eq_2. vm_compute. congruence.
      * destruct (Z.eq_dec i 3) as [Hi_eq_3 | Hi_neq_3].
        { rewrite Hi_eq_3. vm_compute. congruence. }
        destruct (Z.eq_dec i 4) as [Hi_eq_4 | Hi_neq_4].
        { rewrite Hi_eq_4. vm_compute. congruence. }
        destruct (Z.eq_dec i 5) as [Hi_eq_5 | Hi_neq_5].
        { rewrite Hi_eq_5. vm_compute. congruence. }
        destruct (Z.eq_dec i 6) as [Hi_eq_6 | Hi_neq_6].
        { rewrite Hi_eq_6. vm_compute. congruence. }
        destruct (Z.eq_dec i 7) as [Hi_eq_7 | Hi_neq_7].
        { rewrite Hi_eq_7. vm_compute. congruence. }
        destruct (Z.eq_dec i 8) as [Hi_eq_8 | Hi_neq_8].
        { rewrite Hi_eq_8. vm_compute. congruence. }
        destruct (Z.eq_dec i 9) as [Hi_eq_9 | Hi_neq_9].
        { rewrite Hi_eq_9. vm_compute. congruence. }
        assert (i = 10) by lia.
        subst i.
        vm_compute. congruence.
Qed.

Lemma proof_of_fac_entail_wit_1 : fac_entail_wit_1.
Proof.
  unfold fac_entail_wit_1.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_fac_entail_wit_3 : fac_entail_wit_3.
Proof.
  unfold fac_entail_wit_3.
  intros.
  Intros.
  entailer!.
  replace i with ((i - 1) + 1) by lia.
  rewrite factorial_inc by lia.
  replace (i - 1 + 1 - 1) with (i - 1) by lia.
  replace (i - 1 + 1) with i by lia.
  entailer!.
Qed.
