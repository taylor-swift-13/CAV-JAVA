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

(*----- Function bubble_sort -----*)

Definition bubble_sort_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition bubble_sort_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition bubble_sort_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i_2: Z) (lc_2: (@list Z)) (i: Z) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i ))) /\ ((n_pre - i ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i_2 ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((n_pre - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - i )) |]
.

Definition bubble_sort_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc_2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition bubble_sort_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition bubble_sort_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
  **  ((( &( "t" ) )) # Int  |-> (Znth j lc_2 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
  **  ((( &( "t" ) )) # Int  |-> (Znth j lc_2 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition bubble_sort_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) lc_2 0)) (lc_2)) )
  **  ((( &( "t" ) )) # Int  |-> (Znth j lc_2 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) lc_2 0)) (lc_2)) )
  **  ((( &( "t" ) )) # Int  |-> (Znth j lc_2 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition bubble_sort_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) <= (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) ((Znth j lc_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) lc_2 0)) (lc_2)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition bubble_sort_safety_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i_2: Z) (lc_2: (@list Z)) (i: Z) (j: Z) ,
  [| ((j + 1 ) >= (n_pre - i )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i ))) /\ ((n_pre - i ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i_2 ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition bubble_sort_entail_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - 0 ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition bubble_sort_entail_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (lc_2: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| ((0 + 1 ) <= (n_pre - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i ))) /\ ((n_pre - i ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < 0)) -> ((Znth p_5 lc_2 0) <= (Znth 0 lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
.

Definition bubble_sort_entail_wit_3_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_3: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_3 0) > (Znth (j + 1 ) lc_3 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_3)) = n_pre) |] 
  &&  [| (Permutation l lc_3 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_3 0) <= (Znth q_3 lc_3 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_3 0) <= (Znth q_4 lc_3 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_3 0) <= (Znth j lc_3 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) ((Znth j lc_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) lc_3 0)) (lc_3)))) )
|--
  EX (lc_2: (@list Z)) ,
  [| (0 <= (j + 1 )) |] 
  &&  [| (((j + 1 ) + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < (j + 1 ))) -> ((Znth p_5 lc_2 0) <= (Znth (j + 1 ) lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
.

Definition bubble_sort_entail_wit_3_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_3: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_3 0) <= (Znth (j + 1 ) lc_3 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_3)) = n_pre) |] 
  &&  [| (Permutation l lc_3 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_3 0) <= (Znth q_3 lc_3 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_3 0) <= (Znth q_4 lc_3 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_3 0) <= (Znth j lc_3 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_3 )
|--
  EX (lc_2: (@list Z)) ,
  [| (0 <= (j + 1 )) |] 
  &&  [| (((j + 1 ) + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < (j + 1 ))) -> ((Znth p_5 lc_2 0) <= (Znth (j + 1 ) lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
.

Definition bubble_sort_entail_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (i_2: Z) (lc_3: (@list Z)) (i: Z) (j: Z) ,
  [| ((j + 1 ) >= (n_pre - i )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_3)) = n_pre) |] 
  &&  [| (Permutation l lc_3 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_3 0) <= (Znth q_3 lc_3 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i ))) /\ ((n_pre - i ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_3 0) <= (Znth q_4 lc_3 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_3 0) <= (Znth j lc_3 0))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i_2 ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc_2 0) <= (Znth q lc_2 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc_2 0) <= (Znth q_2 lc_2 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre lc_3 )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - (i + 1 ) ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "j" ) )) # Int  |->_)
.

Definition bubble_sort_return_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i_2 ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (l0: (@list Z)) ,
  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l0 0) <= (Znth j l0 0))) |] 
  &&  [| (Permutation l l0 ) |]
  &&  (IntArray.full a_pre n_pre l0 )
.

Definition bubble_sort_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j lc_2 0))
  **  (IntArray.missing_i a_pre j 0 n_pre lc_2 )
.

Definition bubble_sort_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j + 1 ) lc_2 0))
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre lc_2 )
.

Definition bubble_sort_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j lc_2 0))
  **  (IntArray.missing_i a_pre j 0 n_pre lc_2 )
.

Definition bubble_sort_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j + 1 ) lc_2 0))
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre lc_2 )
.

Definition bubble_sort_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre j 0 n_pre lc_2 )
.

Definition bubble_sort_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) (lc_2: (@list Z)) (i_2: Z) (j: Z) ,
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) lc_2 0)) (lc_2)) )
|--
  [| ((Znth j lc_2 0) > (Znth (j + 1 ) lc_2 0)) |] 
  &&  [| ((j + 1 ) < (n_pre - i_2 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (n_pre - i_2 )) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((n_pre - i_2 ) <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth p_3 lc_2 0) <= (Znth q_3 lc_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 lc_2 0) <= (Znth q_4 lc_2 0))) |] 
  &&  [| forall (p_5: Z) , (((0 <= p_5) /\ (p_5 < j)) -> ((Znth p_5 lc_2 0) <= (Znth j lc_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((n_pre - i ) <= p) /\ (p <= q)) /\ (q < n_pre)) -> ((Znth p lc 0) <= (Znth q lc 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 lc 0) <= (Znth q_2 lc 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 2000) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre (replace_Znth (j) ((Znth (j + 1 ) lc_2 0)) (lc_2)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_bubble_sort_safety_wit_1 : bubble_sort_safety_wit_1.
Axiom proof_of_bubble_sort_safety_wit_2 : bubble_sort_safety_wit_2.
Axiom proof_of_bubble_sort_safety_wit_3 : bubble_sort_safety_wit_3.
Axiom proof_of_bubble_sort_safety_wit_4 : bubble_sort_safety_wit_4.
Axiom proof_of_bubble_sort_safety_wit_5 : bubble_sort_safety_wit_5.
Axiom proof_of_bubble_sort_safety_wit_6 : bubble_sort_safety_wit_6.
Axiom proof_of_bubble_sort_safety_wit_7 : bubble_sort_safety_wit_7.
Axiom proof_of_bubble_sort_safety_wit_8 : bubble_sort_safety_wit_8.
Axiom proof_of_bubble_sort_safety_wit_9 : bubble_sort_safety_wit_9.
Axiom proof_of_bubble_sort_safety_wit_10 : bubble_sort_safety_wit_10.
Axiom proof_of_bubble_sort_safety_wit_11 : bubble_sort_safety_wit_11.
Axiom proof_of_bubble_sort_safety_wit_12 : bubble_sort_safety_wit_12.
Axiom proof_of_bubble_sort_safety_wit_13 : bubble_sort_safety_wit_13.
Axiom proof_of_bubble_sort_safety_wit_14 : bubble_sort_safety_wit_14.
Axiom proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Axiom proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Axiom proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Axiom proof_of_bubble_sort_entail_wit_3_2 : bubble_sort_entail_wit_3_2.
Axiom proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Axiom proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Axiom proof_of_bubble_sort_partial_solve_wit_1 : bubble_sort_partial_solve_wit_1.
Axiom proof_of_bubble_sort_partial_solve_wit_2 : bubble_sort_partial_solve_wit_2.
Axiom proof_of_bubble_sort_partial_solve_wit_3 : bubble_sort_partial_solve_wit_3.
Axiom proof_of_bubble_sort_partial_solve_wit_4 : bubble_sort_partial_solve_wit_4.
Axiom proof_of_bubble_sort_partial_solve_wit_5 : bubble_sort_partial_solve_wit_5.
Axiom proof_of_bubble_sort_partial_solve_wit_6 : bubble_sort_partial_solve_wit_6.

End VC_Correct.
