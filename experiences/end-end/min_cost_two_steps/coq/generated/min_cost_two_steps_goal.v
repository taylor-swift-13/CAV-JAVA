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
Require Import min_cost_two_steps.
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

(*----- Function min_cost_two_steps -----*)

Definition min_cost_two_steps_safety_wit_1 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full cost_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition min_cost_two_steps_safety_wit_2 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full cost_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition min_cost_two_steps_safety_wit_3 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full cost_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition min_cost_two_steps_safety_wit_4 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((Znth 0 l 0) + (Znth 1 l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 0 l 0) + (Znth 1 l 0) )) |]
.

Definition min_cost_two_steps_safety_wit_5 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition min_cost_two_steps_safety_wit_6 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition min_cost_two_steps_safety_wit_7 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |-> ((Znth 0 l 0) + (Znth 1 l 0) ))
  **  ((( &( "prev2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition min_cost_two_steps_safety_wit_8 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (prev1 < prev2) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "cur" ) )) # Int  |->_)
|--
  [| ((prev1 + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (prev1 + (Znth i l 0) )) |]
.

Definition min_cost_two_steps_safety_wit_9 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (prev1 >= prev2) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "cur" ) )) # Int  |->_)
|--
  [| ((prev2 + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (prev2 + (Znth i l 0) )) |]
.

Definition min_cost_two_steps_safety_wit_10 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (prev1 >= prev2) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "prev1" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
  **  ((( &( "cur" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition min_cost_two_steps_safety_wit_11 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (prev1 < prev2) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "prev1" ) )) # Int  |-> (prev1 + (Znth i l 0) ))
  **  ((( &( "cur" ) )) # Int  |-> (prev1 + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition min_cost_two_steps_entail_wit_1 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| ((Znth 0 l 0) = (min_cost_two_steps_spec ((sublist (0) ((2 - 1 )) (l))))) |] 
  &&  [| (((Znth 0 l 0) + (Znth 1 l 0) ) = (min_cost_two_steps_spec ((sublist (0) (2) (l))))) |] 
  &&  [| (0 <= (Znth 0 l 0)) |] 
  &&  [| (0 <= ((Znth 0 l 0) + (Znth 1 l 0) )) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
.

Definition min_cost_two_steps_entail_wit_2_1 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i_2: Z) ,
  [| (prev1 < prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (prev1 + (Znth i_2 l 0) ))
|--
  [| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (((i_2 + 1 ) - 1 )) (l))))) |] 
  &&  [| ((prev1 + (Znth i_2 l 0) ) = (min_cost_two_steps_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (0 <= (prev1 + (Znth i_2 l 0) )) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
.

Definition min_cost_two_steps_entail_wit_2_2 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i_2: Z) ,
  [| (prev1 >= prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (prev2 + (Znth i_2 l 0) ))
|--
  [| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (((i_2 + 1 ) - 1 )) (l))))) |] 
  &&  [| ((prev2 + (Znth i_2 l 0) ) = (min_cost_two_steps_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (0 <= (prev2 + (Znth i_2 l 0) )) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
.

Definition min_cost_two_steps_return_wit_1 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| ((Znth 0 l 0) = (min_cost_two_steps_spec (l))) |]
  &&  (IntArray.full cost_pre n_pre l )
.

Definition min_cost_two_steps_return_wit_2 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (prev1 = (min_cost_two_steps_spec (l))) |]
  &&  (IntArray.full cost_pre n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_1 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (n_pre = 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i cost_pre 0 0 n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_2 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i cost_pre 0 0 n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_3 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i cost_pre 0 0 n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_4 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 l 0))
  **  (IntArray.missing_i cost_pre 1 0 n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_5 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i_2: Z) ,
  [| (prev1 < prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (prev1 < prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i cost_pre i_2 0 n_pre l )
.

Definition min_cost_two_steps_partial_solve_wit_6 := 
forall (cost_pre: Z) (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i_2: Z) ,
  [| (prev1 >= prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full cost_pre n_pre l )
|--
  [| (prev1 >= prev2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (sum ((sublist (0) (k_2) (l))))) /\ ((sum ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| forall (k_3: Z) , (((1 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (min_cost_two_steps_spec ((sublist (0) (k_3) (l))))) /\ ((min_cost_two_steps_spec ((sublist (0) (k_3) (l)))) <= (sum ((sublist (0) (k_3) (l))))))) |] 
  &&  [| (prev2 = (min_cost_two_steps_spec ((sublist (0) ((i_2 - 1 )) (l))))) |] 
  &&  [| (prev1 = (min_cost_two_steps_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 <= prev2) |] 
  &&  [| (0 <= prev1) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((1 <= k) /\ (k <= n_pre)) -> ((0 <= (sum ((sublist (0) (k) (l))))) /\ ((sum ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((cost_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i cost_pre i_2 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_min_cost_two_steps_safety_wit_1 : min_cost_two_steps_safety_wit_1.
Axiom proof_of_min_cost_two_steps_safety_wit_2 : min_cost_two_steps_safety_wit_2.
Axiom proof_of_min_cost_two_steps_safety_wit_3 : min_cost_two_steps_safety_wit_3.
Axiom proof_of_min_cost_two_steps_safety_wit_4 : min_cost_two_steps_safety_wit_4.
Axiom proof_of_min_cost_two_steps_safety_wit_5 : min_cost_two_steps_safety_wit_5.
Axiom proof_of_min_cost_two_steps_safety_wit_6 : min_cost_two_steps_safety_wit_6.
Axiom proof_of_min_cost_two_steps_safety_wit_7 : min_cost_two_steps_safety_wit_7.
Axiom proof_of_min_cost_two_steps_safety_wit_8 : min_cost_two_steps_safety_wit_8.
Axiom proof_of_min_cost_two_steps_safety_wit_9 : min_cost_two_steps_safety_wit_9.
Axiom proof_of_min_cost_two_steps_safety_wit_10 : min_cost_two_steps_safety_wit_10.
Axiom proof_of_min_cost_two_steps_safety_wit_11 : min_cost_two_steps_safety_wit_11.
Axiom proof_of_min_cost_two_steps_entail_wit_1 : min_cost_two_steps_entail_wit_1.
Axiom proof_of_min_cost_two_steps_entail_wit_2_1 : min_cost_two_steps_entail_wit_2_1.
Axiom proof_of_min_cost_two_steps_entail_wit_2_2 : min_cost_two_steps_entail_wit_2_2.
Axiom proof_of_min_cost_two_steps_return_wit_1 : min_cost_two_steps_return_wit_1.
Axiom proof_of_min_cost_two_steps_return_wit_2 : min_cost_two_steps_return_wit_2.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_1 : min_cost_two_steps_partial_solve_wit_1.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_2 : min_cost_two_steps_partial_solve_wit_2.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_3 : min_cost_two_steps_partial_solve_wit_3.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_4 : min_cost_two_steps_partial_solve_wit_4.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_5 : min_cost_two_steps_partial_solve_wit_5.
Axiom proof_of_min_cost_two_steps_partial_solve_wit_6 : min_cost_two_steps_partial_solve_wit_6.

End VC_Correct.
