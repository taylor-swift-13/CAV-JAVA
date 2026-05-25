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
From SimpleC.EE.CAV.verify_20260422_062136_array_negate Require Import array_negate_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_negate_safety_wit_1 : array_negate_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_array_negate_safety_wit_3 : array_negate_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_array_negate_partial_solve_wit_1 : array_negate_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_array_negate_partial_solve_wit_2 : array_negate_partial_solve_wit_2.
Proof. Admitted. 

