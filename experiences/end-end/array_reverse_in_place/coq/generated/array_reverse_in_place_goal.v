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
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function array_reverse_in_place -----*)

Definition array_reverse_in_place_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_reverse_in_place_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition array_reverse_in_place_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_reverse_in_place_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (right) ((Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((replace_Znth (left) ((Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))))))) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0))
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((left + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (left + 1 )) |]
.

Definition array_reverse_in_place_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (right) ((Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((replace_Znth (left) ((Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))))))) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0))
  **  ((( &( "left" ) )) # Int  |-> (left + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((right - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (right - 1 )) |]
.

Definition array_reverse_in_place_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= ((n_pre - 1 ) + 1 )) |] 
  &&  [| ((n_pre - 1 ) = ((n_pre - 1 ) - 0 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - 0 )) (n_pre) (l))))) ((app ((sublist (0) (((n_pre - 1 ) + 1 )) (l))) ((rev ((sublist (0) (0) (l)))))))) )
.

Definition array_reverse_in_place_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (right) ((Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((replace_Znth (left) ((Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))))))) )
|--
  [| (0 <= (left + 1 )) |] 
  &&  [| ((left + 1 ) <= n_pre) |] 
  &&  [| ((left + 1 ) <= ((right - 1 ) + 1 )) |] 
  &&  [| ((right - 1 ) = ((n_pre - 1 ) - (left + 1 ) )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - (left + 1 ) )) (n_pre) (l))))) ((app ((sublist ((left + 1 )) (((right - 1 ) + 1 )) (l))) ((rev ((sublist (0) ((left + 1 )) (l)))))))) )
.

Definition array_reverse_in_place_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
|--
  (IntArray.full a_pre n_pre (rev (l)) )
.

Definition array_reverse_in_place_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (left * sizeof(INT) ) )) # Int  |-> (Znth left (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0))
  **  (IntArray.missing_i a_pre left 0 n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
.

Definition array_reverse_in_place_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (right * sizeof(INT) ) )) # Int  |-> (Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0))
  **  (IntArray.missing_i a_pre right 0 n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
.

Definition array_reverse_in_place_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (left * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre left 0 n_pre (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) )
.

Definition array_reverse_in_place_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (left) ((Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))))) )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (right * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre right 0 n_pre (replace_Znth (left) ((Znth right (app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))) 0)) ((app ((rev ((sublist ((n_pre - left )) (n_pre) (l))))) ((app ((sublist (left) ((right + 1 )) (l))) ((rev ((sublist (0) (left) (l)))))))))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_reverse_in_place_safety_wit_1 : array_reverse_in_place_safety_wit_1.
Axiom proof_of_array_reverse_in_place_safety_wit_2 : array_reverse_in_place_safety_wit_2.
Axiom proof_of_array_reverse_in_place_safety_wit_3 : array_reverse_in_place_safety_wit_3.
Axiom proof_of_array_reverse_in_place_safety_wit_4 : array_reverse_in_place_safety_wit_4.
Axiom proof_of_array_reverse_in_place_safety_wit_5 : array_reverse_in_place_safety_wit_5.
Axiom proof_of_array_reverse_in_place_entail_wit_1 : array_reverse_in_place_entail_wit_1.
Axiom proof_of_array_reverse_in_place_entail_wit_2 : array_reverse_in_place_entail_wit_2.
Axiom proof_of_array_reverse_in_place_return_wit_1 : array_reverse_in_place_return_wit_1.
Axiom proof_of_array_reverse_in_place_partial_solve_wit_1 : array_reverse_in_place_partial_solve_wit_1.
Axiom proof_of_array_reverse_in_place_partial_solve_wit_2 : array_reverse_in_place_partial_solve_wit_2.
Axiom proof_of_array_reverse_in_place_partial_solve_wit_3 : array_reverse_in_place_partial_solve_wit_3.
Axiom proof_of_array_reverse_in_place_partial_solve_wit_4 : array_reverse_in_place_partial_solve_wit_4.

End VC_Correct.
