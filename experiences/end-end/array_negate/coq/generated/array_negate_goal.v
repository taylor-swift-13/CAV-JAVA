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

(*----- Function array_negate -----*)

Definition array_negate_safety_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_negate_safety_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i ))) -> ((Znth t_2 l2 0) = (Znth (i + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= (-(Znth i_2 la 0))) /\ ((-(Znth i_2 la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  [| ((Znth i la 0) <> (INT_MIN)) |]
.

Definition array_negate_safety_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i ))) -> ((Znth t_2 l2 0) = (Znth (i + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= (-(Znth i_2 la 0))) /\ ((-(Znth i_2 la 0)) <= INT_MAX))) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) ((-(Znth i la 0))) ((app (l1) (l2)))) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_negate_entail_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
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
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < 0)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - 0 ))) -> ((Znth t_2 l2 0) = (Znth (0 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_negate_entail_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1_2)) = i_2) |] 
  &&  [| ((Zlength (l2_2)) = (n_pre - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((Znth t l1_2 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_2 ))) -> ((Znth t_2 l2_2 0) = (Znth (i_2 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i_2) ((-(Znth i_2 la 0))) ((app (l1_2) (l2_2)))) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = (i_2 + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n_pre - (i_2 + 1 ) )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < (i_2 + 1 ))) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - (i_2 + 1 ) ))) -> ((Znth t_2 l2 0) = (Znth ((i_2 + 1 ) + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_negate_return_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_3: Z) ,
  [| (i_3 >= n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_3) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_3 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_3)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_3 ))) -> ((Znth t_2 l2 0) = (Znth (i_3 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= (-(Znth i_2 la 0))) /\ ((-(Znth i_2 la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = (-(Znth i la 0)))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_negate_partial_solve_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_2 ))) -> ((Znth t_2 l2 0) = (Znth (i_2 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_2 ))) -> ((Znth t_2 l2 0) = (Znth (i_2 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 la 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_negate_partial_solve_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_2 ))) -> ((Znth t_2 l2 0) = (Znth (i_2 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((Znth t l1 0) = (-(Znth t la 0)))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (n_pre - i_2 ))) -> ((Znth t_2 l2 0) = (Znth (i_2 + t_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= (-(Znth i la 0))) /\ ((-(Znth i la 0)) <= INT_MAX))) |]
  &&  (((out_pre + (i_2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre i_2 0 n_pre (app (l1) (l2)) )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_negate_safety_wit_1 : array_negate_safety_wit_1.
Axiom proof_of_array_negate_safety_wit_2 : array_negate_safety_wit_2.
Axiom proof_of_array_negate_safety_wit_3 : array_negate_safety_wit_3.
Axiom proof_of_array_negate_entail_wit_1 : array_negate_entail_wit_1.
Axiom proof_of_array_negate_entail_wit_2 : array_negate_entail_wit_2.
Axiom proof_of_array_negate_return_wit_1 : array_negate_return_wit_1.
Axiom proof_of_array_negate_partial_solve_wit_1 : array_negate_partial_solve_wit_1.
Axiom proof_of_array_negate_partial_solve_wit_2 : array_negate_partial_solve_wit_2.

End VC_Correct.
