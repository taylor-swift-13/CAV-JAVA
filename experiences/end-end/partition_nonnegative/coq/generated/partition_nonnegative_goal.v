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

(*----- Function partition_nonnegative -----*)

Definition partition_nonnegative_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition partition_nonnegative_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition partition_nonnegative_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition partition_nonnegative_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition partition_nonnegative_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) < 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |->_)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition partition_nonnegative_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth i lc 0)) ((replace_Znth (i) ((Znth j lc 0)) (lc)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "tmp" ) )) # Int  |-> (Znth i lc 0))
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition partition_nonnegative_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= ((n_pre - 1 ) + 1 )) |] 
  &&  [| ((-1) <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , ((((n_pre - 1 ) < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition partition_nonnegative_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc_2 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc_2 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) >= 0)) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (j) ((Znth i lc_2 0)) ((replace_Znth (i) ((Znth j lc_2 0)) (lc_2)))) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth i lc_2 0))
|--
  EX (lc: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= ((j - 1 ) + 1 )) |] 
  &&  [| ((-1) <= (j - 1 )) |] 
  &&  [| ((j - 1 ) < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , ((((j - 1 ) < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "tmp" ) )) # Int  |->_)
.

Definition partition_nonnegative_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc_2 0) < 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc_2 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) >= 0)) |] 
  &&  [| (Permutation l lc_2 ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition partition_nonnegative_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| (i > j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lc 0) < 0)) |] 
  &&  [| forall (k_4: Z) , (((j < k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) >= 0)) |] 
  &&  [| (Permutation l lr ) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition partition_nonnegative_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lc 0))
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition partition_nonnegative_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lc 0))
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition partition_nonnegative_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j lc 0))
  **  (IntArray.missing_i a_pre j 0 n_pre lc )
.

Definition partition_nonnegative_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition partition_nonnegative_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth j lc 0)) (lc)) )
|--
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i <= j) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (j + 1 )) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lc 0) < 0)) |] 
  &&  [| forall (k_2: Z) , (((j < k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) >= 0)) |] 
  &&  [| (Permutation l lc ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre j 0 n_pre (replace_Znth (i) ((Znth j lc 0)) (lc)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_partition_nonnegative_safety_wit_1 : partition_nonnegative_safety_wit_1.
Axiom proof_of_partition_nonnegative_safety_wit_2 : partition_nonnegative_safety_wit_2.
Axiom proof_of_partition_nonnegative_safety_wit_3 : partition_nonnegative_safety_wit_3.
Axiom proof_of_partition_nonnegative_safety_wit_4 : partition_nonnegative_safety_wit_4.
Axiom proof_of_partition_nonnegative_safety_wit_5 : partition_nonnegative_safety_wit_5.
Axiom proof_of_partition_nonnegative_safety_wit_6 : partition_nonnegative_safety_wit_6.
Axiom proof_of_partition_nonnegative_entail_wit_1 : partition_nonnegative_entail_wit_1.
Axiom proof_of_partition_nonnegative_entail_wit_2_1 : partition_nonnegative_entail_wit_2_1.
Axiom proof_of_partition_nonnegative_entail_wit_2_2 : partition_nonnegative_entail_wit_2_2.
Axiom proof_of_partition_nonnegative_return_wit_1 : partition_nonnegative_return_wit_1.
Axiom proof_of_partition_nonnegative_partial_solve_wit_1 : partition_nonnegative_partial_solve_wit_1.
Axiom proof_of_partition_nonnegative_partial_solve_wit_2 : partition_nonnegative_partial_solve_wit_2.
Axiom proof_of_partition_nonnegative_partial_solve_wit_3 : partition_nonnegative_partial_solve_wit_3.
Axiom proof_of_partition_nonnegative_partial_solve_wit_4 : partition_nonnegative_partial_solve_wit_4.
Axiom proof_of_partition_nonnegative_partial_solve_wit_5 : partition_nonnegative_partial_solve_wit_5.

End VC_Correct.
