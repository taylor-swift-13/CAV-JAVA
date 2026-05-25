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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function min_of_three -----*)

Definition min_of_three_return_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre >= b_pre) |] 
  &&  [| (b_pre < a_pre) |]
  &&  emp
|--
  ([| (b_pre = a_pre) |] 
  &&  [| (b_pre <= a_pre) |] 
  &&  [| (b_pre <= b_pre) |] 
  &&  [| (b_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (b_pre = b_pre) |] 
  &&  [| (b_pre <= a_pre) |] 
  &&  [| (b_pre <= b_pre) |] 
  &&  [| (b_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (b_pre = c_pre) |] 
  &&  [| (b_pre <= a_pre) |] 
  &&  [| (b_pre <= b_pre) |] 
  &&  [| (b_pre <= c_pre) |]
  &&  emp)
.

Definition min_of_three_return_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre >= a_pre) |] 
  &&  [| (b_pre >= a_pre) |]
  &&  emp
|--
  ([| (a_pre = a_pre) |] 
  &&  [| (a_pre <= a_pre) |] 
  &&  [| (a_pre <= b_pre) |] 
  &&  [| (a_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| (a_pre <= a_pre) |] 
  &&  [| (a_pre <= b_pre) |] 
  &&  [| (a_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (a_pre = c_pre) |] 
  &&  [| (a_pre <= a_pre) |] 
  &&  [| (a_pre <= b_pre) |] 
  &&  [| (a_pre <= c_pre) |]
  &&  emp)
.

Definition min_of_three_return_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre < a_pre) |] 
  &&  [| (b_pre >= a_pre) |]
  &&  emp
|--
  ([| (c_pre = a_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (c_pre = b_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (c_pre = c_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
.

Definition min_of_three_return_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre < b_pre) |] 
  &&  [| (b_pre < a_pre) |]
  &&  emp
|--
  ([| (c_pre = a_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (c_pre = b_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
  ||
  ([| (c_pre = c_pre) |] 
  &&  [| (c_pre <= a_pre) |] 
  &&  [| (c_pre <= b_pre) |] 
  &&  [| (c_pre <= c_pre) |]
  &&  emp)
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_min_of_three_return_wit_1 : min_of_three_return_wit_1.
Axiom proof_of_min_of_three_return_wit_2 : min_of_three_return_wit_2.
Axiom proof_of_min_of_three_return_wit_3 : min_of_three_return_wit_3.
Axiom proof_of_min_of_three_return_wit_4 : min_of_three_return_wit_4.

End VC_Correct.
