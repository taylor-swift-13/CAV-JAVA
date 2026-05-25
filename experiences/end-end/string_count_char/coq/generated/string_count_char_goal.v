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
Require Import string_count_char.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function string_count_char -----*)

Definition string_count_char_safety_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_char_safety_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_char_safety_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_count_char_safety_wit_4 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_char_safety_wit_5 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((ret + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + 1 )) |]
.

Definition string_count_char_safety_wit_6 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_char_safety_wit_7 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_char_entail_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (0 = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_entail_wit_2_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1_2) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= (ret + 1 )) |] 
  &&  [| ((ret + 1 ) <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((ret + 1 ) = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_entail_wit_2_2 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1_2) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_entail_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1_2) (c_pre))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth k_3 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= ret) |] 
  &&  [| (ret <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l) (c_pre))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_return_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) ,
  [| (0 <= ret) |] 
  &&  [| (ret <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l) (c_pre))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (ret = (string_count_char_spec (l) (c_pre))) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_partial_solve_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_char_partial_solve_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (ret: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= ret) |] 
  &&  [| (ret <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (ret = (string_count_char_spec (l1) (c_pre))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_count_char_safety_wit_1 : string_count_char_safety_wit_1.
Axiom proof_of_string_count_char_safety_wit_2 : string_count_char_safety_wit_2.
Axiom proof_of_string_count_char_safety_wit_3 : string_count_char_safety_wit_3.
Axiom proof_of_string_count_char_safety_wit_4 : string_count_char_safety_wit_4.
Axiom proof_of_string_count_char_safety_wit_5 : string_count_char_safety_wit_5.
Axiom proof_of_string_count_char_safety_wit_6 : string_count_char_safety_wit_6.
Axiom proof_of_string_count_char_safety_wit_7 : string_count_char_safety_wit_7.
Axiom proof_of_string_count_char_entail_wit_1 : string_count_char_entail_wit_1.
Axiom proof_of_string_count_char_entail_wit_2_1 : string_count_char_entail_wit_2_1.
Axiom proof_of_string_count_char_entail_wit_2_2 : string_count_char_entail_wit_2_2.
Axiom proof_of_string_count_char_entail_wit_3 : string_count_char_entail_wit_3.
Axiom proof_of_string_count_char_return_wit_1 : string_count_char_return_wit_1.
Axiom proof_of_string_count_char_partial_solve_wit_1 : string_count_char_partial_solve_wit_1.
Axiom proof_of_string_count_char_partial_solve_wit_2 : string_count_char_partial_solve_wit_2.

End VC_Correct.
