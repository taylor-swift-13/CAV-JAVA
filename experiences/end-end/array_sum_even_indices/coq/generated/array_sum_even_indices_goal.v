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
Require Import array_sum_even_indices.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function array_sum_even_indices -----*)

Definition array_sum_even_indices_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sum_even_indices_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sum_even_indices_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((INT_MIN <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition array_sum_even_indices_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_sum_even_indices_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sum_even_indices_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((INT_MIN <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((sum + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (Znth i l 0) )) |]
.

Definition array_sum_even_indices_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((INT_MIN <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_sum_even_indices_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((INT_MIN <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_sum_even_indices_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (array_sum_even_indices_spec ((sublist (0) (0) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_even_indices_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i_2: Z) ,
  [| ((i_2 % ( 2 ) ) = 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((sum + (Znth i_2 l 0) ) = (array_sum_even_indices_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_even_indices_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i_2: Z) ,
  [| ((i_2 % ( 2 ) ) <> 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_even_indices_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((INT_MIN <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i = n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_even_indices_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (sum: Z) ,
  [| (i = n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (sum = (array_sum_even_indices_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_even_indices_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i_2: Z) ,
  [| ((i_2 % ( 2 ) ) = 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((i_2 % ( 2 ) ) = 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (sum = (array_sum_even_indices_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((INT_MIN <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((INT_MIN <= (array_sum_even_indices_spec ((sublist (0) (k) (l))))) /\ ((array_sum_even_indices_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_sum_even_indices_safety_wit_1 : array_sum_even_indices_safety_wit_1.
Axiom proof_of_array_sum_even_indices_safety_wit_2 : array_sum_even_indices_safety_wit_2.
Axiom proof_of_array_sum_even_indices_safety_wit_3 : array_sum_even_indices_safety_wit_3.
Axiom proof_of_array_sum_even_indices_safety_wit_4 : array_sum_even_indices_safety_wit_4.
Axiom proof_of_array_sum_even_indices_safety_wit_5 : array_sum_even_indices_safety_wit_5.
Axiom proof_of_array_sum_even_indices_safety_wit_6 : array_sum_even_indices_safety_wit_6.
Axiom proof_of_array_sum_even_indices_safety_wit_7 : array_sum_even_indices_safety_wit_7.
Axiom proof_of_array_sum_even_indices_safety_wit_8 : array_sum_even_indices_safety_wit_8.
Axiom proof_of_array_sum_even_indices_entail_wit_1 : array_sum_even_indices_entail_wit_1.
Axiom proof_of_array_sum_even_indices_entail_wit_2_1 : array_sum_even_indices_entail_wit_2_1.
Axiom proof_of_array_sum_even_indices_entail_wit_2_2 : array_sum_even_indices_entail_wit_2_2.
Axiom proof_of_array_sum_even_indices_entail_wit_3 : array_sum_even_indices_entail_wit_3.
Axiom proof_of_array_sum_even_indices_return_wit_1 : array_sum_even_indices_return_wit_1.
Axiom proof_of_array_sum_even_indices_partial_solve_wit_1 : array_sum_even_indices_partial_solve_wit_1.

End VC_Correct.
