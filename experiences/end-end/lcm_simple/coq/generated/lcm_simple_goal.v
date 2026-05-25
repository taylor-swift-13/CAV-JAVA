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
Require Import lcm_simple.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function lcm_simple -----*)

Definition lcm_simple_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (x: Z) (k: Z) ,
  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| (x = (a_pre * k )) |] 
  &&  [| (x <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| ((x <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition lcm_simple_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (x: Z) (k: Z) ,
  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| (x = (a_pre * k )) |] 
  &&  [| (x <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition lcm_simple_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (x: Z) (k: Z) ,
  [| ((x % ( b_pre ) ) <> 0) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| (x = (a_pre * k )) |] 
  &&  [| (x <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| ((x + a_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x + a_pre )) |]
.

Definition lcm_simple_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  emp
|--
  EX (k: Z) ,
  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| (a_pre = (a_pre * k )) |] 
  &&  [| (a_pre <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  emp
.

Definition lcm_simple_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (x: Z) (k_2: Z) ,
  [| ((x % ( b_pre ) ) <> 0) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k_2) |] 
  &&  [| (x = (a_pre * k_2 )) |] 
  &&  [| (x <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  emp
|--
  EX (k: Z) ,
  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| ((x + a_pre ) = (a_pre * k )) |] 
  &&  [| ((x + a_pre ) <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  emp
.

Definition lcm_simple_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (x: Z) (k: Z) ,
  [| ((x % ( b_pre ) ) = 0) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |] 
  &&  [| (1 <= k) |] 
  &&  [| (x = (a_pre * k )) |] 
  &&  [| (x <= (lcm_simple_value (a_pre) (b_pre))) |] 
  &&  [| (1 <= a_pre) |] 
  &&  [| (1 <= b_pre) |] 
  &&  [| ((lcm_simple_value (a_pre) (b_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (lcm_simple_spec a_pre b_pre x ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_lcm_simple_safety_wit_1 : lcm_simple_safety_wit_1.
Axiom proof_of_lcm_simple_safety_wit_2 : lcm_simple_safety_wit_2.
Axiom proof_of_lcm_simple_safety_wit_3 : lcm_simple_safety_wit_3.
Axiom proof_of_lcm_simple_entail_wit_1 : lcm_simple_entail_wit_1.
Axiom proof_of_lcm_simple_entail_wit_2 : lcm_simple_entail_wit_2.
Axiom proof_of_lcm_simple_return_wit_1 : lcm_simple_return_wit_1.

End VC_Correct.
