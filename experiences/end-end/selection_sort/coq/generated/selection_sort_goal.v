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

(*----- Function selection_sort -----*)

Definition selection_sort_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "tmp" ) )) # Int  |->_)
  **  ((( &( "min_idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition selection_sort_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "tmp" ) )) # Int  |->_)
  **  ((( &( "min_idx" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition selection_sort_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "tmp" ) )) # Int  |->_)
  **  ((( &( "min_idx" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition selection_sort_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_inner 0) >= (Znth min_idx l_inner 0)) |] 
  &&  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "min_idx" ) )) # Int  |-> min_idx)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |->_)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition selection_sort_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_inner 0) < (Znth min_idx l_inner 0)) |] 
  &&  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "min_idx" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |->_)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition selection_sort_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i_2: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i)) /\ (i <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i_2)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (min_idx) ((Znth i l_inner 0)) ((replace_Znth (i) ((Znth min_idx l_inner 0)) (l_inner)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "min_idx" ) )) # Int  |-> min_idx)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |-> (Znth i l_inner 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition selection_sort_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (l_outer: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < 0)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < 0)) /\ (0 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
.

Definition selection_sort_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
|--
  EX (l_inner: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((i + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (i <= i) |] 
  &&  [| (i < (i + 1 )) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i)) /\ (i <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i <= k) /\ (k < (i + 1 ))) -> ((Znth i l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
.

Definition selection_sort_entail_wit_3_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner_2: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_inner_2 0) < (Znth min_idx l_inner_2 0)) |] 
  &&  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner_2)) = n_pre) |] 
  &&  [| (Permutation l l_inner_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner_2 0) <= (Znth q_3 l_inner_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner_2 0) <= (Znth q_4 l_inner_2 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner_2 0) <= (Znth k l_inner_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner_2 )
|--
  EX (l_inner: (@list Z)) ,
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= n_pre) |] 
  &&  [| (i_2 <= j) |] 
  &&  [| (j < (j + 1 )) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < (j + 1 ))) -> ((Znth j l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
.

Definition selection_sort_entail_wit_3_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner_2: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_inner_2 0) >= (Znth min_idx l_inner_2 0)) |] 
  &&  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner_2)) = n_pre) |] 
  &&  [| (Permutation l l_inner_2 ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner_2 0) <= (Znth q_3 l_inner_2 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner_2 0) <= (Znth q_4 l_inner_2 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner_2 0) <= (Znth k l_inner_2 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner_2 )
|--
  EX (l_inner: (@list Z)) ,
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < (j + 1 )) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < (j + 1 ))) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
.

Definition selection_sort_entail_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer_2: (@list Z)) (i_2: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i)) /\ (i <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l_outer_2)) = n_pre) |] 
  &&  [| (Permutation l l_outer_2 ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i_2)) -> ((Znth p l_outer_2 0) <= (Znth q l_outer_2 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer_2 0) <= (Znth q_2 l_outer_2 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (min_idx) ((Znth i l_inner 0)) ((replace_Znth (i) ((Znth min_idx l_inner 0)) (l_inner)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "min_idx" ) )) # Int  |-> min_idx)
  **  ((( &( "tmp" ) )) # Int  |-> (Znth i l_inner 0))
|--
  EX (l_outer: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < (i + 1 ))) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (i + 1 ))) /\ ((i + 1 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "tmp" ) )) # Int  |->_)
  **  ((( &( "min_idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
.

Definition selection_sort_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i_2)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i lr 0) <= (Znth j lr 0))) |] 
  &&  [| (Permutation l lr ) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition selection_sort_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
|--
  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l_inner 0))
  **  (IntArray.missing_i a_pre j 0 n_pre l_inner )
.

Definition selection_sort_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
|--
  [| (j < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (min_idx * sizeof(INT) ) )) # Int  |-> (Znth min_idx l_inner 0))
  **  (IntArray.missing_i a_pre min_idx 0 n_pre l_inner )
.

Definition selection_sort_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
|--
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l_inner 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l_inner )
.

Definition selection_sort_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
|--
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (min_idx * sizeof(INT) ) )) # Int  |-> (Znth min_idx l_inner 0))
  **  (IntArray.missing_i a_pre min_idx 0 n_pre l_inner )
.

Definition selection_sort_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_inner )
|--
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre i_2 0 n_pre l_inner )
.

Definition selection_sort_partial_solve_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_inner: (@list Z)) (min_idx: Z) (j: Z) (i_2: Z) ,
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i_2) ((Znth min_idx l_inner 0)) (l_inner)) )
|--
  [| (j >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= n_pre) |] 
  &&  [| (i_2 <= min_idx) |] 
  &&  [| (min_idx < j) |] 
  &&  [| ((Zlength (l_inner)) = n_pre) |] 
  &&  [| (Permutation l l_inner ) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , ((((0 <= p_3) /\ (p_3 <= q_3)) /\ (q_3 < i_2)) -> ((Znth p_3 l_inner 0) <= (Znth q_3 l_inner 0))) |] 
  &&  [| forall (p_4: Z) , forall (q_4: Z) , (((((0 <= p_4) /\ (p_4 < i_2)) /\ (i_2 <= q_4)) /\ (q_4 < n_pre)) -> ((Znth p_4 l_inner 0) <= (Znth q_4 l_inner 0))) |] 
  &&  [| forall (k: Z) , (((i_2 <= k) /\ (k < j)) -> ((Znth min_idx l_inner 0) <= (Znth k l_inner 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p <= q)) /\ (q < i)) -> ((Znth p l_outer 0) <= (Znth q l_outer 0))) |] 
  &&  [| forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i)) /\ (i <= q_2)) /\ (q_2 < n_pre)) -> ((Znth p_2 l_outer 0) <= (Znth q_2 l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (min_idx * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre min_idx 0 n_pre (replace_Znth (i_2) ((Znth min_idx l_inner 0)) (l_inner)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_selection_sort_safety_wit_1 : selection_sort_safety_wit_1.
Axiom proof_of_selection_sort_safety_wit_2 : selection_sort_safety_wit_2.
Axiom proof_of_selection_sort_safety_wit_3 : selection_sort_safety_wit_3.
Axiom proof_of_selection_sort_safety_wit_4 : selection_sort_safety_wit_4.
Axiom proof_of_selection_sort_safety_wit_5 : selection_sort_safety_wit_5.
Axiom proof_of_selection_sort_safety_wit_6 : selection_sort_safety_wit_6.
Axiom proof_of_selection_sort_entail_wit_1 : selection_sort_entail_wit_1.
Axiom proof_of_selection_sort_entail_wit_2 : selection_sort_entail_wit_2.
Axiom proof_of_selection_sort_entail_wit_3_1 : selection_sort_entail_wit_3_1.
Axiom proof_of_selection_sort_entail_wit_3_2 : selection_sort_entail_wit_3_2.
Axiom proof_of_selection_sort_entail_wit_4 : selection_sort_entail_wit_4.
Axiom proof_of_selection_sort_return_wit_1 : selection_sort_return_wit_1.
Axiom proof_of_selection_sort_partial_solve_wit_1 : selection_sort_partial_solve_wit_1.
Axiom proof_of_selection_sort_partial_solve_wit_2 : selection_sort_partial_solve_wit_2.
Axiom proof_of_selection_sort_partial_solve_wit_3 : selection_sort_partial_solve_wit_3.
Axiom proof_of_selection_sort_partial_solve_wit_4 : selection_sort_partial_solve_wit_4.
Axiom proof_of_selection_sort_partial_solve_wit_5 : selection_sort_partial_solve_wit_5.
Axiom proof_of_selection_sort_partial_solve_wit_6 : selection_sort_partial_solve_wit_6.

End VC_Correct.
