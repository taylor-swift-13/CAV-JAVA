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

(*----- Function array_add -----*)

Definition array_add_safety_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) /\ (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_add_safety_wit_2 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lo 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) |]
.

Definition array_add_safety_wit_3 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l1' 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full b_pre n_pre lb )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full out_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (lo)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_add_entail_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) /\ (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre lo )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = (n_pre - 0 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - 0 ))) -> ((Znth k_2 l2 0) = (Znth (0 + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) /\ (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_add_entail_wit_2 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i_2: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i_2 + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i_2 + 1 ))) -> ((Znth k_3 l1' 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1_2)) = i_2) |] 
  &&  [| ((Zlength (l2_2)) = (n_pre - i_2 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l1_2 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i_2 ))) -> ((Znth k_2 l2_2 0) = (Znth (i_2 + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) /\ (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1') ((sublist ((i_2 + 1 )) (n_pre) (lo)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = (i_2 + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n_pre - (i_2 + 1 ) )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i_2 + 1 ))) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - (i_2 + 1 ) ))) -> ((Znth k_2 l2 0) = (Znth ((i_2 + 1 ) + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((INT_MIN) <= ((Znth i la 0) + (Znth i lb 0) )) /\ (((Znth i la 0) + (Znth i lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_add_return_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_3: Z) ,
  [| (i_3 >= n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_3) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_3 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_3)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i_3 ))) -> ((Znth k_2 l2 0) = (Znth (i_3 + k_2 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = ((Znth i la 0) + (Znth i lb 0) ))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_add_partial_solve_wit_1_pure := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |]
.

Definition array_add_partial_solve_wit_1_aux := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
.

Definition array_add_partial_solve_wit_1 := array_add_partial_solve_wit_1_pure -> array_add_partial_solve_wit_1_aux.

Definition array_add_partial_solve_wit_2_pure := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i la 0) + (Znth i lb 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |]
.

Definition array_add_partial_solve_wit_2_aux := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i la 0) + (Znth i lb 0) ))
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 la 0) + (Znth k_3 lb 0) ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((INT_MIN) <= ((Znth i_2 la 0) + (Znth i_2 lb 0) )) /\ (((Znth i_2 la 0) + (Znth i_2 lb 0) ) <= INT_MAX))) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i la 0) + (Znth i lb 0) ))
.

Definition array_add_partial_solve_wit_2 := array_add_partial_solve_wit_2_pure -> array_add_partial_solve_wit_2_aux.

Definition array_add_which_implies_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k la 0) + (Znth k lb 0) ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) lo 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1) (l2)) )
|--
  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lo 0))
.

Definition array_add_which_implies_wit_2 := 
forall (out_pre: Z) (b_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lb))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1 0) = ((Znth k_2 la 0) + (Znth k_2 lb 0) ))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre - i ))) -> ((Znth k_3 l2 0) = (Znth (i + k_3 ) lo 0))) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) (l2)) )
  **  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i la 0) + (Znth i lb 0) ))
|--
  EX (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1' 0) = ((Znth k la 0) + (Znth k lb 0) ))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full out_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (lo)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_add_safety_wit_1 : array_add_safety_wit_1.
Axiom proof_of_array_add_safety_wit_2 : array_add_safety_wit_2.
Axiom proof_of_array_add_safety_wit_3 : array_add_safety_wit_3.
Axiom proof_of_array_add_entail_wit_1 : array_add_entail_wit_1.
Axiom proof_of_array_add_entail_wit_2 : array_add_entail_wit_2.
Axiom proof_of_array_add_return_wit_1 : array_add_return_wit_1.
Axiom proof_of_array_add_partial_solve_wit_1_pure : array_add_partial_solve_wit_1_pure.
Axiom proof_of_array_add_partial_solve_wit_1 : array_add_partial_solve_wit_1.
Axiom proof_of_array_add_partial_solve_wit_2_pure : array_add_partial_solve_wit_2_pure.
Axiom proof_of_array_add_partial_solve_wit_2 : array_add_partial_solve_wit_2.
Axiom proof_of_array_add_which_implies_wit_1 : array_add_which_implies_wit_1.
Axiom proof_of_array_add_which_implies_wit_2 : array_add_which_implies_wit_2.

End VC_Correct.
