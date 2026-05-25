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

(*----- Function rotate_left_by_one -----*)

Definition rotate_left_by_one_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "first" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rotate_left_by_one_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "first" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rotate_left_by_one_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition rotate_left_by_one_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rotate_left_by_one_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition rotate_left_by_one_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rotate_left_by_one_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i + 1 ) (app (l1) ((sublist (i) (n_pre) (l)))) 0)) ((app (l1) ((sublist (i) (n_pre) (l)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition rotate_left_by_one_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i >= (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition rotate_left_by_one_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i >= (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rotate_left_by_one_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Znth 0 l 0) = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app (l1) ((sublist (0) (n_pre) (l)))) )
.

Definition rotate_left_by_one_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1_2 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i + 1 ) (app (l1_2) ((sublist (i) (n_pre) (l)))) 0)) ((app (l1_2) ((sublist (i) (n_pre) (l)))))) )
|--
  EX (l1: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app (l1) ((sublist ((i + 1 )) (n_pre) (l)))) )
.

Definition rotate_left_by_one_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i_2: Z) ,
  [| (i_2 >= (n_pre - 1 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((n_pre - 1 )) (first) ((app (l1) ((sublist (i_2) (n_pre) (l)))))) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((i < (n_pre - 1 )) -> ((Znth i lr 0) = (Znth (i + 1 ) l 0))) /\ ((i = (n_pre - 1 )) -> ((Znth i lr 0) = (Znth 0 l 0))))) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition rotate_left_by_one_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition rotate_left_by_one_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((i + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i + 1 ) (app (l1) ((sublist (i) (n_pre) (l)))) 0))
  **  (IntArray.missing_i a_pre (i + 1 ) 0 n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
.

Definition rotate_left_by_one_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (i < (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
.

Definition rotate_left_by_one_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l1: (@list Z)) (first: Z) (i: Z) ,
  [| (i >= (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
|--
  [| (i >= (n_pre - 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n_pre - 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (first = (Znth 0 l 0)) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth (k + 1 ) l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((n_pre - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (n_pre - 1 ) 0 n_pre (app (l1) ((sublist (i) (n_pre) (l)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_rotate_left_by_one_safety_wit_1 : rotate_left_by_one_safety_wit_1.
Axiom proof_of_rotate_left_by_one_safety_wit_2 : rotate_left_by_one_safety_wit_2.
Axiom proof_of_rotate_left_by_one_safety_wit_3 : rotate_left_by_one_safety_wit_3.
Axiom proof_of_rotate_left_by_one_safety_wit_4 : rotate_left_by_one_safety_wit_4.
Axiom proof_of_rotate_left_by_one_safety_wit_5 : rotate_left_by_one_safety_wit_5.
Axiom proof_of_rotate_left_by_one_safety_wit_6 : rotate_left_by_one_safety_wit_6.
Axiom proof_of_rotate_left_by_one_safety_wit_7 : rotate_left_by_one_safety_wit_7.
Axiom proof_of_rotate_left_by_one_safety_wit_8 : rotate_left_by_one_safety_wit_8.
Axiom proof_of_rotate_left_by_one_safety_wit_9 : rotate_left_by_one_safety_wit_9.
Axiom proof_of_rotate_left_by_one_entail_wit_1 : rotate_left_by_one_entail_wit_1.
Axiom proof_of_rotate_left_by_one_entail_wit_2 : rotate_left_by_one_entail_wit_2.
Axiom proof_of_rotate_left_by_one_return_wit_1 : rotate_left_by_one_return_wit_1.
Axiom proof_of_rotate_left_by_one_partial_solve_wit_1 : rotate_left_by_one_partial_solve_wit_1.
Axiom proof_of_rotate_left_by_one_partial_solve_wit_2 : rotate_left_by_one_partial_solve_wit_2.
Axiom proof_of_rotate_left_by_one_partial_solve_wit_3 : rotate_left_by_one_partial_solve_wit_3.
Axiom proof_of_rotate_left_by_one_partial_solve_wit_4 : rotate_left_by_one_partial_solve_wit_4.

End VC_Correct.
