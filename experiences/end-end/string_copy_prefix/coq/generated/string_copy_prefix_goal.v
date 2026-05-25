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
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_copy_prefix -----*)

Definition string_copy_prefix_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_copy_prefix_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((Znth i_2 l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (k_pre + 1 ) (replace_Znth (i) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app (l1) (d1)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_copy_prefix_safety_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 >= k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_copy_prefix_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) d )
|--
  EX (d1: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - 0 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
.

Definition string_copy_prefix_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1_2: (@list Z)) (l1_2: (@list Z)) (i_2: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (i_2 < k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1_2)) = i_2) |] 
  &&  [| ((Zlength (d1_2)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1_2 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (k_pre + 1 ) (replace_Znth (i_2) ((Znth i_2 (app (l) ((cons (0) (nil)))) 0)) ((app (l1_2) (d1_2)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (d1: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = (i_2 + 1 )) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - (i_2 + 1 ) )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (i_2 + 1 ))) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
.

Definition string_copy_prefix_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (i_2 >= k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (k_pre + 1 ) (replace_Znth (k_pre) (0) ((app (l1) (d1)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app ((sublist (0) (k_pre) (l))) ((cons (0) (nil)))) )
.

Definition string_copy_prefix_partial_solve_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 < k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (i_2 < k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (((src_pre + (i_2 * sizeof(CHAR) ) )) # Char  |-> (Znth i_2 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i src_pre i_2 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
.

Definition string_copy_prefix_partial_solve_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (i_2 < k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (i_2 < k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (((dst_pre + (i_2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre i_2 0 (k_pre + 1 ) (app (l1) (d1)) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_copy_prefix_partial_solve_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (k_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 >= k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (k_pre + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= (k_pre + 1 )) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (i_2 >= k_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (d1)) = ((k_pre + 1 ) - i_2 )) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n)) -> ((Znth j l 0) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i_2)) -> ((Znth j_2 l1 0) = (Znth j_2 l 0))) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (d)) = (k_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((Znth i l 0) <> 0)) |]
  &&  (((dst_pre + (k_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre k_pre 0 (k_pre + 1 ) (app (l1) (d1)) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_copy_prefix_safety_wit_1 : string_copy_prefix_safety_wit_1.
Axiom proof_of_string_copy_prefix_safety_wit_2 : string_copy_prefix_safety_wit_2.
Axiom proof_of_string_copy_prefix_safety_wit_3 : string_copy_prefix_safety_wit_3.
Axiom proof_of_string_copy_prefix_entail_wit_1 : string_copy_prefix_entail_wit_1.
Axiom proof_of_string_copy_prefix_entail_wit_2 : string_copy_prefix_entail_wit_2.
Axiom proof_of_string_copy_prefix_return_wit_1 : string_copy_prefix_return_wit_1.
Axiom proof_of_string_copy_prefix_partial_solve_wit_1 : string_copy_prefix_partial_solve_wit_1.
Axiom proof_of_string_copy_prefix_partial_solve_wit_2 : string_copy_prefix_partial_solve_wit_2.
Axiom proof_of_string_copy_prefix_partial_solve_wit_3 : string_copy_prefix_partial_solve_wit_3.

End VC_Correct.
