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
Require Import count_positive.
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

(*----- Function count_positive -----*)

Definition count_positive_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_positive_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_positive_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_positive_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i l 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((cnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt + 1 )) |]
.

Definition count_positive_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i l 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_positive_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i l 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_positive_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (count_positive_spec ((sublist (0) (0) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_positive_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i l 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((cnt + 1 ) = (count_positive_spec ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_positive_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i l 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_positive_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i = n_pre) |] 
  &&  [| (cnt = (count_positive_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_positive_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (cnt: Z) ,
  [| (i = n_pre) |] 
  &&  [| (cnt = (count_positive_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (cnt = (count_positive_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition count_positive_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (cnt: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (cnt = (count_positive_spec ((sublist (0) (i) (l))))) |] 
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

Axiom proof_of_count_positive_safety_wit_1 : count_positive_safety_wit_1.
Axiom proof_of_count_positive_safety_wit_2 : count_positive_safety_wit_2.
Axiom proof_of_count_positive_safety_wit_3 : count_positive_safety_wit_3.
Axiom proof_of_count_positive_safety_wit_4 : count_positive_safety_wit_4.
Axiom proof_of_count_positive_safety_wit_5 : count_positive_safety_wit_5.
Axiom proof_of_count_positive_safety_wit_6 : count_positive_safety_wit_6.
Axiom proof_of_count_positive_entail_wit_1 : count_positive_entail_wit_1.
Axiom proof_of_count_positive_entail_wit_2_1 : count_positive_entail_wit_2_1.
Axiom proof_of_count_positive_entail_wit_2_2 : count_positive_entail_wit_2_2.
Axiom proof_of_count_positive_entail_wit_3 : count_positive_entail_wit_3.
Axiom proof_of_count_positive_return_wit_1 : count_positive_return_wit_1.
Axiom proof_of_count_positive_partial_solve_wit_1 : count_positive_partial_solve_wit_1.

End VC_Correct.
