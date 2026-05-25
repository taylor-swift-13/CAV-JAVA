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

(*----- Function array_swap_ends -----*)

Definition array_swap_ends_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_swap_ends_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_swap_ends_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_swap_ends_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition array_swap_ends_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_swap_ends_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)) )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition array_swap_ends_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)) )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_swap_ends_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((n_pre - 1 )) ((Znth 0 l 0)) ((replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)))) )
|--
  EX (l0: (@list Z)) ,
  [| ((Zlength (l0)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((n_pre < 2) -> ((Znth i l0 0) = (Znth i l 0))) /\ ((n_pre >= 2) -> ((((i = 0) -> ((Znth i l0 0) = (Znth (n_pre - 1 ) l 0))) /\ ((i = (n_pre - 1 )) -> ((Znth i l0 0) = (Znth 0 l 0)))) /\ (((i <> 0) /\ (i <> (n_pre - 1 ))) -> ((Znth i l0 0) = (Znth i l 0))))))) |]
  &&  (IntArray.full a_pre n_pre l0 )
.

Definition array_swap_ends_return_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre < 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (l0: (@list Z)) ,
  [| ((Zlength (l0)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((n_pre < 2) -> ((Znth i l0 0) = (Znth i l 0))) /\ ((n_pre >= 2) -> ((((i = 0) -> ((Znth i l0 0) = (Znth (n_pre - 1 ) l 0))) /\ ((i = (n_pre - 1 )) -> ((Znth i l0 0) = (Znth 0 l 0)))) /\ (((i <> 0) /\ (i <> (n_pre - 1 ))) -> ((Znth i l0 0) = (Znth i l 0))))))) |]
  &&  (IntArray.full a_pre n_pre l0 )
.

Definition array_swap_ends_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_swap_ends_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((n_pre - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (n_pre - 1 ) l 0))
  **  (IntArray.missing_i a_pre (n_pre - 1 ) 0 n_pre l )
.

Definition array_swap_ends_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_swap_ends_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)) )
|--
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((n_pre - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (n_pre - 1 ) 0 n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_swap_ends_safety_wit_1 : array_swap_ends_safety_wit_1.
Axiom proof_of_array_swap_ends_safety_wit_2 : array_swap_ends_safety_wit_2.
Axiom proof_of_array_swap_ends_safety_wit_3 : array_swap_ends_safety_wit_3.
Axiom proof_of_array_swap_ends_safety_wit_4 : array_swap_ends_safety_wit_4.
Axiom proof_of_array_swap_ends_safety_wit_5 : array_swap_ends_safety_wit_5.
Axiom proof_of_array_swap_ends_safety_wit_6 : array_swap_ends_safety_wit_6.
Axiom proof_of_array_swap_ends_safety_wit_7 : array_swap_ends_safety_wit_7.
Axiom proof_of_array_swap_ends_return_wit_1 : array_swap_ends_return_wit_1.
Axiom proof_of_array_swap_ends_return_wit_2 : array_swap_ends_return_wit_2.
Axiom proof_of_array_swap_ends_partial_solve_wit_1 : array_swap_ends_partial_solve_wit_1.
Axiom proof_of_array_swap_ends_partial_solve_wit_2 : array_swap_ends_partial_solve_wit_2.
Axiom proof_of_array_swap_ends_partial_solve_wit_3 : array_swap_ends_partial_solve_wit_3.
Axiom proof_of_array_swap_ends_partial_solve_wit_4 : array_swap_ends_partial_solve_wit_4.

End VC_Correct.
