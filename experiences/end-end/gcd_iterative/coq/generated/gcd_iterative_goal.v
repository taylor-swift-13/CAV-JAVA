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
Require Import gcd_iterative.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function gcd_iterative -----*)

Definition gcd_iterative_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (g: Z) (b: Z) (a: Z) ,
  [| (0 <= a) |] 
  &&  [| (0 <= b) |] 
  &&  [| (0 < (a + b )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (gcd_iterative_spec a b g ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "r" ) )) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition gcd_iterative_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (g: Z) (b: Z) (a: Z) ,
  [| (b <> 0) |] 
  &&  [| (0 <= a) |] 
  &&  [| (0 <= b) |] 
  &&  [| (0 < (a + b )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (gcd_iterative_spec a b g ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "r" ) )) # Int  |->_)
|--
  [| ((a <> (INT_MIN)) \/ (b <> (-1))) |] 
  &&  [| (b <> 0) |]
.

Definition gcd_iterative_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  emp
|--
  EX (g: Z) ,
  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  emp
.

Definition gcd_iterative_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (g_2: Z) (b: Z) (a: Z) ,
  [| (b <> 0) |] 
  &&  [| (0 <= a) |] 
  &&  [| (0 <= b) |] 
  &&  [| (0 < (a + b )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g_2 ) |] 
  &&  [| (gcd_iterative_spec a b g_2 ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  ((( &( "r" ) )) # Int  |-> (a % ( b ) ))
|--
  EX (g: Z) ,
  [| (0 <= b) |] 
  &&  [| (0 <= (a % ( b ) )) |] 
  &&  [| (0 < (b + (a % ( b ) ) )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (gcd_iterative_spec b (a % ( b ) ) g ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  ((( &( "r" ) )) # Int  |->_)
.

Definition gcd_iterative_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (g: Z) (b: Z) (a: Z) ,
  [| (b = 0) |] 
  &&  [| (0 <= a) |] 
  &&  [| (0 <= b) |] 
  &&  [| (0 < (a + b )) |] 
  &&  [| (gcd_iterative_spec a_pre b_pre g ) |] 
  &&  [| (gcd_iterative_spec a b g ) |] 
  &&  [| (0 <= a_pre) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (0 < (a_pre + b_pre )) |]
  &&  emp
|--
  [| (gcd_iterative_spec a_pre b_pre a ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_gcd_iterative_safety_wit_1 : gcd_iterative_safety_wit_1.
Axiom proof_of_gcd_iterative_safety_wit_2 : gcd_iterative_safety_wit_2.
Axiom proof_of_gcd_iterative_entail_wit_1 : gcd_iterative_entail_wit_1.
Axiom proof_of_gcd_iterative_entail_wit_2 : gcd_iterative_entail_wit_2.
Axiom proof_of_gcd_iterative_return_wit_1 : gcd_iterative_return_wit_1.

End VC_Correct.
