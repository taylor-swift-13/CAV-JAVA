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

(*----- Function string_reverse_copy -----*)

Definition string_reverse_copy_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_reverse_copy_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (((n_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((n_pre - 1 ) - i )) |]
.

Definition string_reverse_copy_safety_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition string_reverse_copy_safety_wit_4 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_reverse_copy_safety_wit_5 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n_pre + 1 ) (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0)) ((app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))))) )
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_reverse_copy_safety_wit_6 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_reverse_copy_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) d )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - 0 )) (n_pre) (l))))) ((sublist (0) ((n_pre + 1 )) (d)))) )
.

Definition string_reverse_copy_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n_pre + 1 ) (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0)) ((app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))))) )
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - (i + 1 ) )) (n_pre) (l))))) ((sublist ((i + 1 )) ((n_pre + 1 )) (d)))) )
.

Definition string_reverse_copy_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n_pre + 1 ) (replace_Znth (n_pre) (0) ((app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))))) )
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev (l))) ((cons (0) (nil)))) )
.

Definition string_reverse_copy_partial_solve_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (((src_pre + (((n_pre - 1 ) - i ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((n_pre - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i src_pre ((n_pre - 1 ) - i ) 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
.

Definition string_reverse_copy_partial_solve_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (((dst_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre i 0 (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_reverse_copy_partial_solve_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (d: (@list Z)) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((Zlength (d)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (((dst_pre + (n_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre n_pre 0 (n_pre + 1 ) (app ((rev ((sublist ((n_pre - i )) (n_pre) (l))))) ((sublist (i) ((n_pre + 1 )) (d)))) )
  **  (CharArray.full src_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_reverse_copy_safety_wit_1 : string_reverse_copy_safety_wit_1.
Axiom proof_of_string_reverse_copy_safety_wit_2 : string_reverse_copy_safety_wit_2.
Axiom proof_of_string_reverse_copy_safety_wit_3 : string_reverse_copy_safety_wit_3.
Axiom proof_of_string_reverse_copy_safety_wit_4 : string_reverse_copy_safety_wit_4.
Axiom proof_of_string_reverse_copy_safety_wit_5 : string_reverse_copy_safety_wit_5.
Axiom proof_of_string_reverse_copy_safety_wit_6 : string_reverse_copy_safety_wit_6.
Axiom proof_of_string_reverse_copy_entail_wit_1 : string_reverse_copy_entail_wit_1.
Axiom proof_of_string_reverse_copy_entail_wit_2 : string_reverse_copy_entail_wit_2.
Axiom proof_of_string_reverse_copy_return_wit_1 : string_reverse_copy_return_wit_1.
Axiom proof_of_string_reverse_copy_partial_solve_wit_1 : string_reverse_copy_partial_solve_wit_1.
Axiom proof_of_string_reverse_copy_partial_solve_wit_2 : string_reverse_copy_partial_solve_wit_2.
Axiom proof_of_string_reverse_copy_partial_solve_wit_3 : string_reverse_copy_partial_solve_wit_3.

End VC_Correct.
