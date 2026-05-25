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
Require Import house_robber.
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

(*----- Function house_robber -----*)

Definition house_robber_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition house_robber_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition house_robber_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |-> 0)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition house_robber_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (prev2 = 0)) |] 
  &&  [| ((i > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i - 1 )) (l)))))) |] 
  &&  [| ((i < n_pre) -> ((prev2 + (Znth i l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "take" ) )) # Int  |->_)
|--
  [| ((prev2 + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (prev2 + (Znth i l 0) )) |]
.

Definition house_robber_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) ,
  [| ((prev2 + (Znth i l 0) ) <= prev1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (prev2 = 0)) |] 
  &&  [| ((i > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i - 1 )) (l)))))) |] 
  &&  [| ((i < n_pre) -> ((prev2 + (Znth i l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "cur" ) )) # Int  |-> prev1)
  **  ((( &( "take" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition house_robber_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) ,
  [| ((prev2 + (Znth i l 0) ) > prev1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (prev2 = 0)) |] 
  &&  [| ((i > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i - 1 )) (l)))))) |] 
  &&  [| ((i < n_pre) -> ((prev2 + (Znth i l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "prev1" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "cur" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
  **  ((( &( "take" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition house_robber_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (0 = (house_robber_spec ((sublist (0) (0) (l))))) |] 
  &&  [| ((0 = 0) -> (0 = 0)) |] 
  &&  [| ((0 > 0) -> (0 = (house_robber_spec ((sublist (0) ((0 - 1 )) (l)))))) |] 
  &&  [| ((0 < n_pre) -> ((0 + (Znth 0 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition house_robber_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i_2: Z) ,
  [| ((prev2 + (Znth i_2 l 0) ) > prev1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| ((i_2 = 0) -> (prev2 = 0)) |] 
  &&  [| ((i_2 > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i_2 - 1 )) (l)))))) |] 
  &&  [| ((i_2 < n_pre) -> ((prev2 + (Znth i_2 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (prev2 + (Znth i_2 l 0) ))
  **  ((( &( "take" ) )) # Int  |-> (prev2 + (Znth i_2 l 0) ))
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| ((prev2 + (Znth i_2 l 0) ) = (house_robber_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (((i_2 + 1 ) = 0) -> (prev1 = 0)) |] 
  &&  [| (((i_2 + 1 ) > 0) -> (prev1 = (house_robber_spec ((sublist (0) (((i_2 + 1 ) - 1 )) (l)))))) |] 
  &&  [| (((i_2 + 1 ) < n_pre) -> ((prev1 + (Znth (i_2 + 1 ) l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "take" ) )) # Int  |->_)
.

Definition house_robber_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i_2: Z) ,
  [| ((prev2 + (Znth i_2 l 0) ) <= prev1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| ((i_2 = 0) -> (prev2 = 0)) |] 
  &&  [| ((i_2 > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i_2 - 1 )) (l)))))) |] 
  &&  [| ((i_2 < n_pre) -> ((prev2 + (Znth i_2 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> prev1)
  **  ((( &( "take" ) )) # Int  |-> (prev2 + (Znth i_2 l 0) ))
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (((i_2 + 1 ) = 0) -> (prev1 = 0)) |] 
  &&  [| (((i_2 + 1 ) > 0) -> (prev1 = (house_robber_spec ((sublist (0) (((i_2 + 1 ) - 1 )) (l)))))) |] 
  &&  [| (((i_2 + 1 ) < n_pre) -> ((prev1 + (Znth (i_2 + 1 ) l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "take" ) )) # Int  |->_)
.

Definition house_robber_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| ((i_2 = 0) -> (prev2 = 0)) |] 
  &&  [| ((i_2 > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i_2 - 1 )) (l)))))) |] 
  &&  [| ((i_2 < n_pre) -> ((prev2 + (Znth i_2 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (prev1 = (house_robber_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition house_robber_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| ((i_2 = 0) -> (prev2 = 0)) |] 
  &&  [| ((i_2 > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i_2 - 1 )) (l)))))) |] 
  &&  [| ((i_2 < n_pre) -> ((prev2 + (Znth i_2 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < n_pre)) -> ((0 <= (Znth t l 0)) /\ ((Znth t l 0) <= INT_MAX))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k_2) (l))))) /\ ((house_robber_spec ((sublist (0) (k_2) (l)))) <= INT_MAX))) |] 
  &&  [| (prev1 = (house_robber_spec ((sublist (0) (i_2) (l))))) |] 
  &&  [| ((i_2 = 0) -> (prev2 = 0)) |] 
  &&  [| ((i_2 > 0) -> (prev2 = (house_robber_spec ((sublist (0) ((i_2 - 1 )) (l)))))) |] 
  &&  [| ((i_2 < n_pre) -> ((prev2 + (Znth i_2 l 0) ) <= INT_MAX)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) <= INT_MAX))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (house_robber_spec ((sublist (0) (k) (l))))) /\ ((house_robber_spec ((sublist (0) (k) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_house_robber_safety_wit_1 : house_robber_safety_wit_1.
Axiom proof_of_house_robber_safety_wit_2 : house_robber_safety_wit_2.
Axiom proof_of_house_robber_safety_wit_3 : house_robber_safety_wit_3.
Axiom proof_of_house_robber_safety_wit_4 : house_robber_safety_wit_4.
Axiom proof_of_house_robber_safety_wit_5 : house_robber_safety_wit_5.
Axiom proof_of_house_robber_safety_wit_6 : house_robber_safety_wit_6.
Axiom proof_of_house_robber_entail_wit_1 : house_robber_entail_wit_1.
Axiom proof_of_house_robber_entail_wit_2_1 : house_robber_entail_wit_2_1.
Axiom proof_of_house_robber_entail_wit_2_2 : house_robber_entail_wit_2_2.
Axiom proof_of_house_robber_return_wit_1 : house_robber_return_wit_1.
Axiom proof_of_house_robber_partial_solve_wit_1 : house_robber_partial_solve_wit_1.

End VC_Correct.
