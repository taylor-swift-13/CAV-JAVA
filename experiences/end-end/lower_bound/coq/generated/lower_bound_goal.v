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

(*----- Function lower_bound -----*)

Definition lower_bound_safety_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition lower_bound_safety_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < left)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((right <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
|--
  [| ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) |]
.

Definition lower_bound_safety_wit_3 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < left)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((right <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
|--
  [| (((right - left ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition lower_bound_safety_wit_4 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < left)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((right <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
|--
  [| ((right - left ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (right - left )) |]
.

Definition lower_bound_safety_wit_5 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < left)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((right <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition lower_bound_safety_wit_6 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (mid: Z) ,
  [| ((Znth mid l 0) < target_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < left)) -> ((Znth i_2 l 0) < target_pre)) |] 
  &&  [| forall (i_3: Z) , (((right <= i_3) /\ (i_3 < n_pre)) -> (target_pre <= (Znth i_3 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
|--
  [| ((mid + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (mid + 1 )) |]
.

Definition lower_bound_safety_wit_7 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (mid: Z) ,
  [| ((Znth mid l 0) < target_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < left)) -> ((Znth i_2 l 0) < target_pre)) |] 
  &&  [| forall (i_3: Z) , (((right <= i_3) /\ (i_3 < n_pre)) -> (target_pre <= (Znth i_3 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition lower_bound_entail_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < 0)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((n_pre <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition lower_bound_entail_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_3: Z) , ((((0 <= i_5) /\ (i_5 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < left)) -> ((Znth i_6 l 0) < target_pre)) |] 
  &&  [| forall (i_7: Z) , (((right <= i_7) /\ (i_7 < n_pre)) -> (target_pre <= (Znth i_7 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_4: Z) , forall (j_2: Z) , ((((0 <= i_4) /\ (i_4 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_4 l 0) <= (Znth j_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= (left + ((right - left ) ÷ 2 ) )) |] 
  &&  [| ((left + ((right - left ) ÷ 2 ) ) < n_pre) |] 
  &&  [| (left <= (left + ((right - left ) ÷ 2 ) )) |] 
  &&  [| ((left + ((right - left ) ÷ 2 ) ) < right) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < left)) -> ((Znth i_2 l 0) < target_pre)) |] 
  &&  [| forall (i_3: Z) , (((right <= i_3) /\ (i_3 < n_pre)) -> (target_pre <= (Znth i_3 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition lower_bound_entail_wit_3_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (mid: Z) ,
  [| ((Znth mid l 0) >= target_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_3: Z) , ((((0 <= i_5) /\ (i_5 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < left)) -> ((Znth i_6 l 0) < target_pre)) |] 
  &&  [| forall (i_7: Z) , (((right <= i_7) /\ (i_7 < n_pre)) -> (target_pre <= (Znth i_7 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |-> mid)
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < left)) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((mid <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
.

Definition lower_bound_entail_wit_3_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (mid: Z) ,
  [| ((Znth mid l 0) < target_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_3: Z) , ((((0 <= i_5) /\ (i_5 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < left)) -> ((Znth i_6 l 0) < target_pre)) |] 
  &&  [| forall (i_7: Z) , (((right <= i_7) /\ (i_7 < n_pre)) -> (target_pre <= (Znth i_7 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |-> mid)
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= (mid + 1 )) |] 
  &&  [| ((mid + 1 ) <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (mid + 1 ))) -> ((Znth i_3 l 0) < target_pre)) |] 
  &&  [| forall (i_4: Z) , (((right <= i_4) /\ (i_4 < n_pre)) -> (target_pre <= (Znth i_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "mid" ) )) # Int  |->_)
.

Definition lower_bound_return_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_4: Z) , forall (j_2: Z) , ((((0 <= i_4) /\ (i_4 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_4 l 0) <= (Znth j_2 l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < left)) -> ((Znth i_5 l 0) < target_pre)) |] 
  &&  [| forall (i_6: Z) , (((right <= i_6) /\ (i_6 < n_pre)) -> (target_pre <= (Znth i_6 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j: Z) , ((((0 <= i_3) /\ (i_3 <= j)) /\ (j < n_pre)) -> ((Znth i_3 l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < left)) -> ((Znth i l 0) < target_pre)) |] 
  &&  [| forall (i_2: Z) , (((left <= i_2) /\ (i_2 < n_pre)) -> (target_pre <= (Znth i_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition lower_bound_partial_solve_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (mid: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < left)) -> ((Znth i_2 l 0) < target_pre)) |] 
  &&  [| forall (i_3: Z) , (((right <= i_3) /\ (i_3 < n_pre)) -> (target_pre <= (Znth i_3 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right <= n_pre) |] 
  &&  [| (0 <= mid) |] 
  &&  [| (mid < n_pre) |] 
  &&  [| (left <= mid) |] 
  &&  [| (mid < right) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < left)) -> ((Znth i_2 l 0) < target_pre)) |] 
  &&  [| forall (i_3: Z) , (((right <= i_3) /\ (i_3 < n_pre)) -> (target_pre <= (Znth i_3 l 0))) |]
  &&  (((a_pre + (mid * sizeof(INT) ) )) # Int  |-> (Znth mid l 0))
  **  (IntArray.missing_i a_pre mid 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_lower_bound_safety_wit_1 : lower_bound_safety_wit_1.
Axiom proof_of_lower_bound_safety_wit_2 : lower_bound_safety_wit_2.
Axiom proof_of_lower_bound_safety_wit_3 : lower_bound_safety_wit_3.
Axiom proof_of_lower_bound_safety_wit_4 : lower_bound_safety_wit_4.
Axiom proof_of_lower_bound_safety_wit_5 : lower_bound_safety_wit_5.
Axiom proof_of_lower_bound_safety_wit_6 : lower_bound_safety_wit_6.
Axiom proof_of_lower_bound_safety_wit_7 : lower_bound_safety_wit_7.
Axiom proof_of_lower_bound_entail_wit_1 : lower_bound_entail_wit_1.
Axiom proof_of_lower_bound_entail_wit_2 : lower_bound_entail_wit_2.
Axiom proof_of_lower_bound_entail_wit_3_1 : lower_bound_entail_wit_3_1.
Axiom proof_of_lower_bound_entail_wit_3_2 : lower_bound_entail_wit_3_2.
Axiom proof_of_lower_bound_return_wit_1 : lower_bound_return_wit_1.
Axiom proof_of_lower_bound_partial_solve_wit_1 : lower_bound_partial_solve_wit_1.

End VC_Correct.
