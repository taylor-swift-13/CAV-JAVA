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

(*----- Function string_copy -----*)

Definition string_copy_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_copy_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_copy_safety_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_copy_safety_wit_4 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n + 1 ) (replace_Znth (i) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app (l1) (d1)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_copy_safety_wit_5 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_copy_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) d )
|--
  EX (d1: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - 0 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
.

Definition string_copy_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1_2: (@list Z)) (l1_2: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (d1_2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1_2 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n + 1 ) (replace_Znth (i) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app (l1_2) (d1_2)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (d1: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - (i + 1 ) )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
.

Definition string_copy_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full dst_pre (n + 1 ) (replace_Znth (i) (0) ((app (l1) (d1)))) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_copy_partial_solve_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((src_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i src_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
.

Definition string_copy_partial_solve_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((src_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i src_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
.

Definition string_copy_partial_solve_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((dst_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre i 0 (n + 1 ) (app (l1) (d1)) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_copy_partial_solve_wit_4 := 
forall (dst_pre: Z) (src_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full dst_pre (n + 1 ) (app (l1) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((dst_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i dst_pre i 0 (n + 1 ) (app (l1) (d1)) )
  **  (CharArray.full src_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_copy_safety_wit_1 : string_copy_safety_wit_1.
Axiom proof_of_string_copy_safety_wit_2 : string_copy_safety_wit_2.
Axiom proof_of_string_copy_safety_wit_3 : string_copy_safety_wit_3.
Axiom proof_of_string_copy_safety_wit_4 : string_copy_safety_wit_4.
Axiom proof_of_string_copy_safety_wit_5 : string_copy_safety_wit_5.
Axiom proof_of_string_copy_entail_wit_1 : string_copy_entail_wit_1.
Axiom proof_of_string_copy_entail_wit_2 : string_copy_entail_wit_2.
Axiom proof_of_string_copy_return_wit_1 : string_copy_return_wit_1.
Axiom proof_of_string_copy_partial_solve_wit_1 : string_copy_partial_solve_wit_1.
Axiom proof_of_string_copy_partial_solve_wit_2 : string_copy_partial_solve_wit_2.
Axiom proof_of_string_copy_partial_solve_wit_3 : string_copy_partial_solve_wit_3.
Axiom proof_of_string_copy_partial_solve_wit_4 : string_copy_partial_solve_wit_4.

End VC_Correct.
