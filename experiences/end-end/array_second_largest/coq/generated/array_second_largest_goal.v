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

(*----- Function array_second_largest -----*)

Definition array_second_largest_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  ((( &( "max1" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_second_largest_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  ((( &( "max2" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "max1" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_second_largest_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "max2" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "max1" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_second_largest_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "max2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "max1" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_second_largest_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) <= max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max1" ) )) # Int  |-> max1)
  **  ((( &( "max2" ) )) # Int  |-> max2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max1" ) )) # Int  |-> max1)
  **  ((( &( "max2" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max1" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "max2" ) )) # Int  |-> max1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_entail_wit_1_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < 2) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < 2) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = (Znth 1 l 0)) |] 
  &&  [| ((Znth second l 0) = (Znth 0 l 0)) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < 2)) /\ (k <> top)) -> ((Znth k l 0) <= (Znth 0 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_entail_wit_1_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < 2) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < 2) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = (Znth 0 l 0)) |] 
  &&  [| ((Znth second l 0) = (Znth 1 l 0)) |] 
  &&  [| ((Znth 0 l 0) > (Znth 1 l 0)) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < 2)) /\ (k <> top)) -> ((Znth k l 0) <= (Znth 1 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second_2: Z) (top_2: Z) (i: Z) ,
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top_2) |] 
  &&  [| (top_2 < i) |] 
  &&  [| (0 <= second_2) |] 
  &&  [| (second_2 < i) |] 
  &&  [| (top_2 <> second_2) |] 
  &&  [| ((Znth top_2 l 0) = max1) |] 
  &&  [| ((Znth second_2 l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top_2)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < (i + 1 )) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < (i + 1 )) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = (Znth i l 0)) |] 
  &&  [| ((Znth second l 0) = max1) |] 
  &&  [| ((Znth i l 0) > max1) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ (k <> top)) -> ((Znth k l 0) <= max1)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second_2: Z) (top_2: Z) (i: Z) ,
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top_2) |] 
  &&  [| (top_2 < i) |] 
  &&  [| (0 <= second_2) |] 
  &&  [| (second_2 < i) |] 
  &&  [| (top_2 <> second_2) |] 
  &&  [| ((Znth top_2 l 0) = max1) |] 
  &&  [| ((Znth second_2 l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top_2)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < (i + 1 )) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < (i + 1 )) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = (Znth i l 0)) |] 
  &&  [| (max1 > (Znth i l 0)) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ (k <> top)) -> ((Znth k l 0) <= (Znth i l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_entail_wit_2_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second_2: Z) (top_2: Z) (i: Z) ,
  [| ((Znth i l 0) <= max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top_2) |] 
  &&  [| (top_2 < i) |] 
  &&  [| (0 <= second_2) |] 
  &&  [| (second_2 < i) |] 
  &&  [| (top_2 <> second_2) |] 
  &&  [| ((Znth top_2 l 0) = max1) |] 
  &&  [| ((Znth second_2 l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top_2)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < (i + 1 )) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < (i + 1 )) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second_2: Z) (top_2: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top_2) |] 
  &&  [| (top_2 < i_2) |] 
  &&  [| (0 <= second_2) |] 
  &&  [| (second_2 < i_2) |] 
  &&  [| (top_2 <> second_2) |] 
  &&  [| ((Znth top_2 l 0) = max1) |] 
  &&  [| ((Znth second_2 l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i_2)) /\ (k <> top_2)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (second: Z)  (top: Z) ,
  [| (0 <= top) |] 
  &&  [| (top < n_pre) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < n_pre) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| ((Znth top l 0) > max2) |] 
  &&  [| forall (i: Z) , ((((0 <= i) /\ (i < n_pre)) /\ (i <> top)) -> ((Znth i l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 l 0))
  **  (IntArray.missing_i a_pre 1 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max2: Z) (max1: Z) (second: Z) (top: Z) (i: Z) ,
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < n_pre)) -> ((Znth p l 0) <> (Znth q l 0))) |] 
  &&  [| (0 <= top) |] 
  &&  [| (top < i) |] 
  &&  [| (0 <= second) |] 
  &&  [| (second < i) |] 
  &&  [| (top <> second) |] 
  &&  [| ((Znth top l 0) = max1) |] 
  &&  [| ((Znth second l 0) = max2) |] 
  &&  [| (max1 > max2) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ (k <> top)) -> ((Znth k l 0) <= max2)) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_second_largest_safety_wit_1 : array_second_largest_safety_wit_1.
Axiom proof_of_array_second_largest_safety_wit_2 : array_second_largest_safety_wit_2.
Axiom proof_of_array_second_largest_safety_wit_3 : array_second_largest_safety_wit_3.
Axiom proof_of_array_second_largest_safety_wit_4 : array_second_largest_safety_wit_4.
Axiom proof_of_array_second_largest_safety_wit_5 : array_second_largest_safety_wit_5.
Axiom proof_of_array_second_largest_safety_wit_6 : array_second_largest_safety_wit_6.
Axiom proof_of_array_second_largest_safety_wit_7 : array_second_largest_safety_wit_7.
Axiom proof_of_array_second_largest_entail_wit_1_1 : array_second_largest_entail_wit_1_1.
Axiom proof_of_array_second_largest_entail_wit_1_2 : array_second_largest_entail_wit_1_2.
Axiom proof_of_array_second_largest_entail_wit_2_1 : array_second_largest_entail_wit_2_1.
Axiom proof_of_array_second_largest_entail_wit_2_2 : array_second_largest_entail_wit_2_2.
Axiom proof_of_array_second_largest_entail_wit_2_3 : array_second_largest_entail_wit_2_3.
Axiom proof_of_array_second_largest_return_wit_1 : array_second_largest_return_wit_1.
Axiom proof_of_array_second_largest_partial_solve_wit_1 : array_second_largest_partial_solve_wit_1.
Axiom proof_of_array_second_largest_partial_solve_wit_2 : array_second_largest_partial_solve_wit_2.
Axiom proof_of_array_second_largest_partial_solve_wit_3 : array_second_largest_partial_solve_wit_3.
Axiom proof_of_array_second_largest_partial_solve_wit_4 : array_second_largest_partial_solve_wit_4.
Axiom proof_of_array_second_largest_partial_solve_wit_5 : array_second_largest_partial_solve_wit_5.
Axiom proof_of_array_second_largest_partial_solve_wit_6 : array_second_largest_partial_solve_wit_6.

End VC_Correct.
