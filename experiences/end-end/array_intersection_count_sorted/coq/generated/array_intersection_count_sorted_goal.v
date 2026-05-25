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
Require Import array_intersection_count_sorted.
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

(*----- Function array_intersection_count_sorted -----*)

Definition array_intersection_count_sorted_safety_wit_1 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_intersection_count_sorted_safety_wit_2 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_intersection_count_sorted_safety_wit_3 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_intersection_count_sorted_safety_wit_4 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) = (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition array_intersection_count_sorted_safety_wit_5 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i: Z) ,
  [| ((Znth i la 0) = (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((0 <= i_2) /\ (i_2 <= j)) /\ (j < n_pre)) -> ((Znth i_2 la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_3: Z) , forall (j_2: Z) , ((((0 <= i_3) /\ (i_3 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_3 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_intersection_count_sorted_safety_wit_6 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) = (Znth j lb 0)) |] 
  &&  [| (j < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i la 0) <= (Znth j_2 la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_3: Z) , ((((0 <= i_2) /\ (i_2 <= j_3)) /\ (j_3 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_3 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> (i_3 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition array_intersection_count_sorted_safety_wit_7 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i: Z) ,
  [| ((Znth i la 0) < (Znth j_3 lb 0)) |] 
  &&  [| ((Znth i la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((0 <= i_2) /\ (i_2 <= j)) /\ (j < n_pre)) -> ((Znth i_2 la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_3: Z) , forall (j_2: Z) , ((((0 <= i_3) /\ (i_3 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_3 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_intersection_count_sorted_safety_wit_8 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) >= (Znth j lb 0)) |] 
  &&  [| ((Znth i_3 la 0) <> (Znth j lb 0)) |] 
  &&  [| (j < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i la 0) <= (Znth j_2 la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_3: Z) , ((((0 <= i_2) /\ (i_2 <= j_3)) /\ (j_3 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_3 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition array_intersection_count_sorted_entail_wit_1 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((0 + (array_intersection_count_sorted_spec ((sublist (0) (n_pre) (la))) ((sublist (0) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_entail_wit_2_1 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) >= (Znth j_3 lb 0)) |] 
  &&  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= (j_3 + 1 )) |] 
  &&  [| ((j_3 + 1 ) <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= (j_3 + 1 )) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist ((j_3 + 1 )) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_entail_wit_2_2 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) < (Znth j_3 lb 0)) |] 
  &&  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  [| (0 <= (i_3 + 1 )) |] 
  &&  [| ((i_3 + 1 ) <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i_3 + 1 )) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist ((i_3 + 1 )) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_entail_wit_2_3 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) = (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  [| (0 <= (i_3 + 1 )) |] 
  &&  [| ((i_3 + 1 ) <= n_pre) |] 
  &&  [| (0 <= (j_3 + 1 )) |] 
  &&  [| ((j_3 + 1 ) <= m_pre) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i_3 + 1 )) |] 
  &&  [| ((count + 1 ) <= (j_3 + 1 )) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| (((count + 1 ) + (array_intersection_count_sorted_spec ((sublist ((i_3 + 1 )) (n_pre) (la))) ((sublist ((j_3 + 1 )) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_return_wit_1 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| (j_3 >= m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (count = (array_intersection_count_sorted_spec (la) (lb))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_return_wit_2 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| (i_3 >= n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (count = (array_intersection_count_sorted_spec (la) (lb))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_partial_solve_wit_1 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((a_pre + (i_3 * sizeof(INT) ) )) # Int  |-> (Znth i_3 la 0))
  **  (IntArray.missing_i a_pre i_3 0 n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_partial_solve_wit_2 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((b_pre + (j_3 * sizeof(INT) ) )) # Int  |-> (Znth j_3 lb 0))
  **  (IntArray.missing_i b_pre j_3 0 m_pre lb )
  **  (IntArray.full a_pre n_pre la )
.

Definition array_intersection_count_sorted_partial_solve_wit_3 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((a_pre + (i_3 * sizeof(INT) ) )) # Int  |-> (Znth i_3 la 0))
  **  (IntArray.missing_i a_pre i_3 0 n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition array_intersection_count_sorted_partial_solve_wit_4 := 
forall (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (count: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  [| ((Znth i_3 la 0) <> (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i_3) |] 
  &&  [| (count <= j_3) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (x: Z) , forall (y: Z) , ((((0 <= x) /\ (x <= y)) /\ (y < n_pre)) -> ((Znth x la 0) <= (Znth y la 0))) |] 
  &&  [| forall (x_2: Z) , forall (y_2: Z) , ((((0 <= x_2) /\ (x_2 <= y_2)) /\ (y_2 < m_pre)) -> ((Znth x_2 lb 0) <= (Znth y_2 lb 0))) |] 
  &&  [| ((count + (array_intersection_count_sorted_spec ((sublist (i_3) (n_pre) (la))) ((sublist (j_3) (m_pre) (lb)))) ) = (array_intersection_count_sorted_spec (la) (lb))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (m_pre <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((b_pre + (j_3 * sizeof(INT) ) )) # Int  |-> (Znth j_3 lb 0))
  **  (IntArray.missing_i b_pre j_3 0 m_pre lb )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_intersection_count_sorted_safety_wit_1 : array_intersection_count_sorted_safety_wit_1.
Axiom proof_of_array_intersection_count_sorted_safety_wit_2 : array_intersection_count_sorted_safety_wit_2.
Axiom proof_of_array_intersection_count_sorted_safety_wit_3 : array_intersection_count_sorted_safety_wit_3.
Axiom proof_of_array_intersection_count_sorted_safety_wit_4 : array_intersection_count_sorted_safety_wit_4.
Axiom proof_of_array_intersection_count_sorted_safety_wit_5 : array_intersection_count_sorted_safety_wit_5.
Axiom proof_of_array_intersection_count_sorted_safety_wit_6 : array_intersection_count_sorted_safety_wit_6.
Axiom proof_of_array_intersection_count_sorted_safety_wit_7 : array_intersection_count_sorted_safety_wit_7.
Axiom proof_of_array_intersection_count_sorted_safety_wit_8 : array_intersection_count_sorted_safety_wit_8.
Axiom proof_of_array_intersection_count_sorted_entail_wit_1 : array_intersection_count_sorted_entail_wit_1.
Axiom proof_of_array_intersection_count_sorted_entail_wit_2_1 : array_intersection_count_sorted_entail_wit_2_1.
Axiom proof_of_array_intersection_count_sorted_entail_wit_2_2 : array_intersection_count_sorted_entail_wit_2_2.
Axiom proof_of_array_intersection_count_sorted_entail_wit_2_3 : array_intersection_count_sorted_entail_wit_2_3.
Axiom proof_of_array_intersection_count_sorted_return_wit_1 : array_intersection_count_sorted_return_wit_1.
Axiom proof_of_array_intersection_count_sorted_return_wit_2 : array_intersection_count_sorted_return_wit_2.
Axiom proof_of_array_intersection_count_sorted_partial_solve_wit_1 : array_intersection_count_sorted_partial_solve_wit_1.
Axiom proof_of_array_intersection_count_sorted_partial_solve_wit_2 : array_intersection_count_sorted_partial_solve_wit_2.
Axiom proof_of_array_intersection_count_sorted_partial_solve_wit_3 : array_intersection_count_sorted_partial_solve_wit_3.
Axiom proof_of_array_intersection_count_sorted_partial_solve_wit_4 : array_intersection_count_sorted_partial_solve_wit_4.

End VC_Correct.
