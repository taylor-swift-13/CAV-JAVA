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
Require Import digit_sum.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function digit_sum -----*)

Definition digit_sum_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digit_sum_safety_wit_2 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digit_sum_safety_wit_3 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((sum + (n % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (n % ( 10 ) ) )) |]
.

Definition digit_sum_safety_wit_4 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition digit_sum_safety_wit_5 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition digit_sum_safety_wit_6 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (n % ( 10 ) ) ))
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition digit_sum_safety_wit_7 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (n % ( 10 ) ) ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition digit_sum_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |]
  &&  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int  |-> 0)
.

Definition digit_sum_entail_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((0 + n_pre ) <= n_pre) |] 
  &&  [| ((0 + (digit_sum_z (n_pre)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition digit_sum_entail_wit_3 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (0 <= (n ÷ 10 )) |] 
  &&  [| (0 <= (sum + (n % ( 10 ) ) )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (((sum + (n % ( 10 ) ) ) + (n ÷ 10 ) ) <= n_pre) |] 
  &&  [| (((sum + (n % ( 10 ) ) ) + (digit_sum_z ((n ÷ 10 ))) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition digit_sum_return_wit_1 := 
forall (n_pre: Z) (sum: Z) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((sum + n ) <= n_pre) |] 
  &&  [| ((sum + (digit_sum_z (n)) ) = (digit_sum_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (sum = (digit_sum_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_digit_sum_safety_wit_1 : digit_sum_safety_wit_1.
Axiom proof_of_digit_sum_safety_wit_2 : digit_sum_safety_wit_2.
Axiom proof_of_digit_sum_safety_wit_3 : digit_sum_safety_wit_3.
Axiom proof_of_digit_sum_safety_wit_4 : digit_sum_safety_wit_4.
Axiom proof_of_digit_sum_safety_wit_5 : digit_sum_safety_wit_5.
Axiom proof_of_digit_sum_safety_wit_6 : digit_sum_safety_wit_6.
Axiom proof_of_digit_sum_safety_wit_7 : digit_sum_safety_wit_7.
Axiom proof_of_digit_sum_entail_wit_1 : digit_sum_entail_wit_1.
Axiom proof_of_digit_sum_entail_wit_2 : digit_sum_entail_wit_2.
Axiom proof_of_digit_sum_entail_wit_3 : digit_sum_entail_wit_3.
Axiom proof_of_digit_sum_return_wit_1 : digit_sum_return_wit_1.

End VC_Correct.
