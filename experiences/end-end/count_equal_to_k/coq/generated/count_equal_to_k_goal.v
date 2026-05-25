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
Require Import count_equal_to_k.
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

(*----- Function count_equal_to_k -----*)

Definition count_equal_to_k_safety_wit_1 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_equal_to_k_safety_wit_2 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_equal_to_k_safety_wit_3 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i l 0) = k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  [| ((ret + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + 1 )) |]
.

Definition count_equal_to_k_safety_wit_4 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i l 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_equal_to_k_safety_wit_5 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i l 0) = k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_equal_to_k_entail_wit_1 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (count_equal_to_k_spec ((sublist (0) (0) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_equal_to_k_entail_wit_2_1 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i l 0) = k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((ret + 1 ) = (count_equal_to_k_spec ((sublist (0) ((i + 1 )) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_equal_to_k_entail_wit_2_2 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i l 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) ((i + 1 )) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_equal_to_k_entail_wit_3 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i = n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec (l) (k_pre))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_equal_to_k_return_wit_1 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) ,
  [| (i = n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec (l) (k_pre))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (ret = (count_equal_to_k_spec (l) (k_pre))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_equal_to_k_partial_solve_wit_1 := 
forall (k_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (count_equal_to_k_spec ((sublist (0) (i) (l))) (k_pre))) |] 
  &&  [| (0 <= n_pre) |] 
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

Axiom proof_of_count_equal_to_k_safety_wit_1 : count_equal_to_k_safety_wit_1.
Axiom proof_of_count_equal_to_k_safety_wit_2 : count_equal_to_k_safety_wit_2.
Axiom proof_of_count_equal_to_k_safety_wit_3 : count_equal_to_k_safety_wit_3.
Axiom proof_of_count_equal_to_k_safety_wit_4 : count_equal_to_k_safety_wit_4.
Axiom proof_of_count_equal_to_k_safety_wit_5 : count_equal_to_k_safety_wit_5.
Axiom proof_of_count_equal_to_k_entail_wit_1 : count_equal_to_k_entail_wit_1.
Axiom proof_of_count_equal_to_k_entail_wit_2_1 : count_equal_to_k_entail_wit_2_1.
Axiom proof_of_count_equal_to_k_entail_wit_2_2 : count_equal_to_k_entail_wit_2_2.
Axiom proof_of_count_equal_to_k_entail_wit_3 : count_equal_to_k_entail_wit_3.
Axiom proof_of_count_equal_to_k_return_wit_1 : count_equal_to_k_return_wit_1.
Axiom proof_of_count_equal_to_k_partial_solve_wit_1 : count_equal_to_k_partial_solve_wit_1.

End VC_Correct.
