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
Require Import remove_duplicates_sorted.
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

(*----- Function remove_duplicates_sorted -----*)

Definition remove_duplicates_sorted_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_sorted_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_sorted_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_sorted_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  ((( &( "j" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_sorted_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i l 0) <= (Znth j_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition remove_duplicates_sorted_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_sorted_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i_2: Z) ,
  [| ((Znth i_2 lc 0) <> (Znth (j - 1 ) lc 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i l 0) <= (Znth j_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth i_2 lc 0)) (lc)) )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition remove_duplicates_sorted_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i: Z) ,
  [| ((Znth i lc 0) = (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((0 <= i_2) /\ (i_2 <= j)) /\ (j < n_pre)) -> ((Znth i_2 l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_sorted_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i: Z) ,
  [| ((Znth i lc 0) <> (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((0 <= i_2) /\ (i_2 <= j)) /\ (j < n_pre)) -> ((Znth i_2 l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j_2) ((Znth i lc 0)) (lc)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_sorted_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lc: (@list Z)) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (1 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (1) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (1) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((1 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition remove_duplicates_sorted_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| ((Znth i_2 lc_2 0) <> (Znth (j_2 - 1 ) lc_2 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc_2 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j_2) ((Znth i_2 lc_2 0)) (lc_2)) )
|--
  EX (lc: (@list Z)) ,
  [| (1 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (1 <= (j_2 + 1 )) |] 
  &&  [| ((j_2 + 1 ) <= (i_2 + 1 )) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| ((j_2 + 1 ) = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) ((i_2 + 1 )) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (j_2 + 1 ))) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) ((i_2 + 1 )) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , ((((i_2 + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition remove_duplicates_sorted_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| ((Znth i_2 lc_2 0) = (Znth (j_2 - 1 ) lc_2 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc_2 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  EX (lc: (@list Z)) ,
  [| (1 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= (i_2 + 1 )) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) ((i_2 + 1 )) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) ((i_2 + 1 )) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , ((((i_2 + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition remove_duplicates_sorted_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| (0 = (Zlength ((remove_duplicates_sorted_spec (l))))) |] 
  &&  [| ((sublist (0) (0) (lr)) = (remove_duplicates_sorted_spec (l))) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition remove_duplicates_sorted_return_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i l 0) <= (Znth j_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| (j = (Zlength ((remove_duplicates_sorted_spec (l))))) |] 
  &&  [| ((sublist (0) (j) (lr)) = (remove_duplicates_sorted_spec (l))) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition remove_duplicates_sorted_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 lc 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre lc )
.

Definition remove_duplicates_sorted_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (((a_pre + ((j_2 - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j_2 - 1 ) lc 0))
  **  (IntArray.missing_i a_pre (j_2 - 1 ) 0 n_pre lc )
.

Definition remove_duplicates_sorted_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| ((Znth i_2 lc 0) <> (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i_2 lc 0) <> (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 lc 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre lc )
.

Definition remove_duplicates_sorted_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j_2: Z) (i_2: Z) ,
  [| ((Znth i_2 lc 0) <> (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i_2 lc 0) <> (Znth (j_2 - 1 ) lc 0)) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (1 <= j_2) |] 
  &&  [| (j_2 <= i_2) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (j_2 = (Zlength ((remove_duplicates_sorted_spec ((sublist (0) (i_2) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < j_2)) -> ((Znth k lc 0) = (Znth k (remove_duplicates_sorted_spec ((sublist (0) (i_2) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |]
  &&  (((a_pre + (j_2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre j_2 0 n_pre lc )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_remove_duplicates_sorted_safety_wit_1 : remove_duplicates_sorted_safety_wit_1.
Axiom proof_of_remove_duplicates_sorted_safety_wit_2 : remove_duplicates_sorted_safety_wit_2.
Axiom proof_of_remove_duplicates_sorted_safety_wit_3 : remove_duplicates_sorted_safety_wit_3.
Axiom proof_of_remove_duplicates_sorted_safety_wit_4 : remove_duplicates_sorted_safety_wit_4.
Axiom proof_of_remove_duplicates_sorted_safety_wit_5 : remove_duplicates_sorted_safety_wit_5.
Axiom proof_of_remove_duplicates_sorted_safety_wit_6 : remove_duplicates_sorted_safety_wit_6.
Axiom proof_of_remove_duplicates_sorted_safety_wit_7 : remove_duplicates_sorted_safety_wit_7.
Axiom proof_of_remove_duplicates_sorted_safety_wit_8 : remove_duplicates_sorted_safety_wit_8.
Axiom proof_of_remove_duplicates_sorted_safety_wit_9 : remove_duplicates_sorted_safety_wit_9.
Axiom proof_of_remove_duplicates_sorted_entail_wit_1 : remove_duplicates_sorted_entail_wit_1.
Axiom proof_of_remove_duplicates_sorted_entail_wit_2_1 : remove_duplicates_sorted_entail_wit_2_1.
Axiom proof_of_remove_duplicates_sorted_entail_wit_2_2 : remove_duplicates_sorted_entail_wit_2_2.
Axiom proof_of_remove_duplicates_sorted_return_wit_1 : remove_duplicates_sorted_return_wit_1.
Axiom proof_of_remove_duplicates_sorted_return_wit_2 : remove_duplicates_sorted_return_wit_2.
Axiom proof_of_remove_duplicates_sorted_partial_solve_wit_1 : remove_duplicates_sorted_partial_solve_wit_1.
Axiom proof_of_remove_duplicates_sorted_partial_solve_wit_2 : remove_duplicates_sorted_partial_solve_wit_2.
Axiom proof_of_remove_duplicates_sorted_partial_solve_wit_3 : remove_duplicates_sorted_partial_solve_wit_3.
Axiom proof_of_remove_duplicates_sorted_partial_solve_wit_4 : remove_duplicates_sorted_partial_solve_wit_4.

End VC_Correct.
