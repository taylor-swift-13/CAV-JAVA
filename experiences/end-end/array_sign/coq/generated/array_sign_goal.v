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
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_sign -----*)

Definition array_sign_safety_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sign_safety_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (t: Z) , ((((0 <= t) /\ (t < i)) /\ ((Znth t la 0) > 0)) -> ((Znth t l1 0) = 1)) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < i)) /\ ((Znth t_2 la 0) < 0)) -> ((Znth t_2 l1 0) = (-1))) |] 
  &&  [| forall (t_3: Z) , ((((0 <= t_3) /\ (t_3 < i)) /\ ((Znth t_3 la 0) = 0)) -> ((Znth t_3 l1 0) = 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n_pre - i ))) -> ((Znth t_4 l2 0) = (Znth (i + t_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |->_)
|--
  [| False |]
.

Definition array_sign_safety_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (t: Z) , ((((0 <= t) /\ (t < i)) /\ ((Znth t la 0) > 0)) -> ((Znth t l1 0) = 1)) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < i)) /\ ((Znth t_2 la 0) < 0)) -> ((Znth t_2 l1 0) = (-1))) |] 
  &&  [| forall (t_3: Z) , ((((0 <= t_3) /\ (t_3 < i)) /\ ((Znth t_3 la 0) = 0)) -> ((Znth t_3 l1 0) = 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n_pre - i ))) -> ((Znth t_4 l2 0) = (Znth (i + t_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |->_)
|--
  [| False |]
.

Definition array_sign_entail_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = (n_pre - 0 )) |] 
  &&  [| forall (t: Z) , ((((0 <= t) /\ (t < 0)) /\ ((Znth t la 0) > 0)) -> ((Znth t l1 0) = 1)) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < 0)) /\ ((Znth t_2 la 0) < 0)) -> ((Znth t_2 l1 0) = (-1))) |] 
  &&  [| forall (t_3: Z) , ((((0 <= t_3) /\ (t_3 < 0)) /\ ((Znth t_3 la 0) = 0)) -> ((Znth t_3 l1 0) = 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n_pre - 0 ))) -> ((Znth t_4 l2 0) = (Znth (0 + t_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_sign_safety_wit_1 : array_sign_safety_wit_1.
Axiom proof_of_array_sign_safety_wit_2 : array_sign_safety_wit_2.
Axiom proof_of_array_sign_safety_wit_3 : array_sign_safety_wit_3.
Axiom proof_of_array_sign_entail_wit_1 : array_sign_entail_wit_1.

End VC_Correct.
