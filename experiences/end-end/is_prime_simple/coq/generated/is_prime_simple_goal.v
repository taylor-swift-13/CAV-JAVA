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
Require Import is_prime_simple.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function is_prime_simple -----*)

Definition is_prime_simple_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_simple_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre < 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |->_)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_simple_safety_wit_4 := 
forall (n_pre: Z) (d: Z) ,
  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  [| ((n_pre <> (INT_MIN)) \/ (d <> (-1))) |] 
  &&  [| (d <> 0) |]
.

Definition is_prime_simple_safety_wit_5 := 
forall (n_pre: Z) (d: Z) ,
  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_6 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_7 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  [| ((d + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d + 1 )) |]
.

Definition is_prime_simple_safety_wit_8 := 
forall (n_pre: Z) (d: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (d = n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_simple_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |->_)
.

Definition is_prime_simple_entail_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition is_prime_simple_entail_wit_3 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= (d + 1 )) |] 
  &&  [| ((d + 1 ) <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < (d + 1 ))) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition is_prime_simple_entail_wit_4 := 
forall (n_pre: Z) (d: Z) ,
  [| (d >= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k_2: Z) , (((2 <= k_2) /\ (k_2 < d)) -> ((n_pre % ( k_2 ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (2 <= n_pre) |] 
  &&  [| (d = n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)) |]
  &&  emp
.

Definition is_prime_simple_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre < 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (is_prime_simple_spec n_pre 0 ) |]
  &&  emp
.

Definition is_prime_simple_return_wit_2 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < d)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (is_prime_simple_spec n_pre 0 ) |]
  &&  emp
.

Definition is_prime_simple_return_wit_3 := 
forall (n_pre: Z) (d: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (d = n_pre) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)) |]
  &&  emp
|--
  [| (is_prime_simple_spec n_pre 1 ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_prime_simple_safety_wit_1 : is_prime_simple_safety_wit_1.
Axiom proof_of_is_prime_simple_safety_wit_2 : is_prime_simple_safety_wit_2.
Axiom proof_of_is_prime_simple_safety_wit_3 : is_prime_simple_safety_wit_3.
Axiom proof_of_is_prime_simple_safety_wit_4 : is_prime_simple_safety_wit_4.
Axiom proof_of_is_prime_simple_safety_wit_5 : is_prime_simple_safety_wit_5.
Axiom proof_of_is_prime_simple_safety_wit_6 : is_prime_simple_safety_wit_6.
Axiom proof_of_is_prime_simple_safety_wit_7 : is_prime_simple_safety_wit_7.
Axiom proof_of_is_prime_simple_safety_wit_8 : is_prime_simple_safety_wit_8.
Axiom proof_of_is_prime_simple_entail_wit_1 : is_prime_simple_entail_wit_1.
Axiom proof_of_is_prime_simple_entail_wit_2 : is_prime_simple_entail_wit_2.
Axiom proof_of_is_prime_simple_entail_wit_3 : is_prime_simple_entail_wit_3.
Axiom proof_of_is_prime_simple_entail_wit_4 : is_prime_simple_entail_wit_4.
Axiom proof_of_is_prime_simple_return_wit_1 : is_prime_simple_return_wit_1.
Axiom proof_of_is_prime_simple_return_wit_2 : is_prime_simple_return_wit_2.
Axiom proof_of_is_prime_simple_return_wit_3 : is_prime_simple_return_wit_3.

End VC_Correct.
