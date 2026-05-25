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
Require Import majority_candidate.
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

(*----- Function majority_candidate -----*)

Definition majority_candidate_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition majority_candidate_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "candidate" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition majority_candidate_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "count" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "candidate" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition majority_candidate_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition majority_candidate_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (count = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "candidate" ) )) # Int  |-> (Znth i l 0))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition majority_candidate_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) = candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition majority_candidate_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) <> candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  [| ((count - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count - 1 )) |]
.

Definition majority_candidate_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) <> candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition majority_candidate_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) = candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition majority_candidate_safety_wit_10 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (count = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "candidate" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition majority_candidate_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| ((majority_candidate_acc ((Znth 0 l 0)) (1) ((sublist (1) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (count = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((majority_candidate_acc ((Znth i l 0)) (1) ((sublist ((i + 1 )) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) = candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((majority_candidate_acc (candidate) ((count + 1 )) ((sublist ((i + 1 )) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_entail_wit_2_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| ((Znth i l 0) <> candidate) |] 
  &&  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (i + 1 )) |] 
  &&  [| ((majority_candidate_acc (candidate) ((count - 1 )) ((sublist ((i + 1 )) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i = n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (candidate = (majority_candidate_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (count: Z) (candidate: Z) ,
  [| (i = n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (candidate = (majority_candidate_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (candidate = (majority_candidate_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition majority_candidate_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition majority_candidate_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (count = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (count = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition majority_candidate_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (candidate: Z) (count: Z) (i: Z) ,
  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (count <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| ((majority_candidate_acc (candidate) (count) ((sublist (i) (n_pre) (l)))) = (majority_candidate_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_majority_candidate_safety_wit_1 : majority_candidate_safety_wit_1.
Axiom proof_of_majority_candidate_safety_wit_2 : majority_candidate_safety_wit_2.
Axiom proof_of_majority_candidate_safety_wit_3 : majority_candidate_safety_wit_3.
Axiom proof_of_majority_candidate_safety_wit_4 : majority_candidate_safety_wit_4.
Axiom proof_of_majority_candidate_safety_wit_5 : majority_candidate_safety_wit_5.
Axiom proof_of_majority_candidate_safety_wit_6 : majority_candidate_safety_wit_6.
Axiom proof_of_majority_candidate_safety_wit_7 : majority_candidate_safety_wit_7.
Axiom proof_of_majority_candidate_safety_wit_8 : majority_candidate_safety_wit_8.
Axiom proof_of_majority_candidate_safety_wit_9 : majority_candidate_safety_wit_9.
Axiom proof_of_majority_candidate_safety_wit_10 : majority_candidate_safety_wit_10.
Axiom proof_of_majority_candidate_entail_wit_1 : majority_candidate_entail_wit_1.
Axiom proof_of_majority_candidate_entail_wit_2_1 : majority_candidate_entail_wit_2_1.
Axiom proof_of_majority_candidate_entail_wit_2_2 : majority_candidate_entail_wit_2_2.
Axiom proof_of_majority_candidate_entail_wit_2_3 : majority_candidate_entail_wit_2_3.
Axiom proof_of_majority_candidate_entail_wit_3 : majority_candidate_entail_wit_3.
Axiom proof_of_majority_candidate_return_wit_1 : majority_candidate_return_wit_1.
Axiom proof_of_majority_candidate_partial_solve_wit_1 : majority_candidate_partial_solve_wit_1.
Axiom proof_of_majority_candidate_partial_solve_wit_2 : majority_candidate_partial_solve_wit_2.
Axiom proof_of_majority_candidate_partial_solve_wit_3 : majority_candidate_partial_solve_wit_3.

End VC_Correct.
