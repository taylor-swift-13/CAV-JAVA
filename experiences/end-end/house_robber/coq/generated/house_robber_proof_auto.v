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
From SimpleC.EE.CAV.verify_20260422_171952_house_robber Require Import house_robber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import house_robber.
Local Open Scope sac.

Lemma proof_of_house_robber_safety_wit_1 : house_robber_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_house_robber_safety_wit_2 : house_robber_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_house_robber_safety_wit_3 : house_robber_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_house_robber_safety_wit_5 : house_robber_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_house_robber_safety_wit_6 : house_robber_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_house_robber_partial_solve_wit_1 : house_robber_partial_solve_wit_1.
Proof. Admitted. 

