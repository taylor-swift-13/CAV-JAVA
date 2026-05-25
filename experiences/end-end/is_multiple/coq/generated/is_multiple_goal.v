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
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function is_multiple -----*)

Definition is_multiple_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (0 < b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition is_multiple_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (0 < b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_multiple_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (0 < b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_multiple_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| (0 < b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_multiple_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (0 < b_pre) |]
  &&  emp
|--
  ([| (1 = 0) |] 
  &&  [| forall (q: Z) , (a_pre <> (q * b_pre )) |]
  &&  emp)
  ||
  (EX (q_2: Z) ,
  [| (1 = 1) |] 
  &&  [| (a_pre = (q_2 * b_pre )) |]
  &&  emp)
.

Definition is_multiple_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| (0 < b_pre) |]
  &&  emp
|--
  ([| (0 = 0) |] 
  &&  [| forall (q: Z) , (a_pre <> (q * b_pre )) |]
  &&  emp)
  ||
  (EX (q_2: Z) ,
  [| (0 = 1) |] 
  &&  [| (a_pre = (q_2 * b_pre )) |]
  &&  emp)
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_multiple_safety_wit_1 : is_multiple_safety_wit_1.
Axiom proof_of_is_multiple_safety_wit_2 : is_multiple_safety_wit_2.
Axiom proof_of_is_multiple_safety_wit_3 : is_multiple_safety_wit_3.
Axiom proof_of_is_multiple_safety_wit_4 : is_multiple_safety_wit_4.
Axiom proof_of_is_multiple_return_wit_1 : is_multiple_return_wit_1.
Axiom proof_of_is_multiple_return_wit_2 : is_multiple_return_wit_2.

End VC_Correct.
