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
Require Import string_count_spaces.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_count_spaces -----*)

Definition string_count_spaces_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_spaces_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_spaces_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_count_spaces_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_spaces_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition string_count_spaces_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((cnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt + 1 )) |]
.

Definition string_count_spaces_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_spaces_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_spaces_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
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
  &&  [| (0 = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1_2))) |] 
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
  &&  [| (0 <= (cnt + 1 )) |] 
  &&  [| ((cnt + 1 ) <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((cnt + 1 ) = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1_2))) |] 
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
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1_2))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth k_3 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= cnt) |] 
  &&  [| (cnt <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) ,
  [| (0 <= cnt) |] 
  &&  [| (cnt <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (cnt = (string_count_spaces_spec (l))) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_spaces_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (cnt: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
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
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cnt = (string_count_spaces_spec (l1))) |] 
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

Axiom proof_of_string_count_spaces_safety_wit_1 : string_count_spaces_safety_wit_1.
Axiom proof_of_string_count_spaces_safety_wit_2 : string_count_spaces_safety_wit_2.
Axiom proof_of_string_count_spaces_safety_wit_3 : string_count_spaces_safety_wit_3.
Axiom proof_of_string_count_spaces_safety_wit_4 : string_count_spaces_safety_wit_4.
Axiom proof_of_string_count_spaces_safety_wit_5 : string_count_spaces_safety_wit_5.
Axiom proof_of_string_count_spaces_safety_wit_6 : string_count_spaces_safety_wit_6.
Axiom proof_of_string_count_spaces_safety_wit_7 : string_count_spaces_safety_wit_7.
Axiom proof_of_string_count_spaces_safety_wit_8 : string_count_spaces_safety_wit_8.
Axiom proof_of_string_count_spaces_entail_wit_1 : string_count_spaces_entail_wit_1.
Axiom proof_of_string_count_spaces_entail_wit_2_1 : string_count_spaces_entail_wit_2_1.
Axiom proof_of_string_count_spaces_entail_wit_2_2 : string_count_spaces_entail_wit_2_2.
Axiom proof_of_string_count_spaces_entail_wit_3 : string_count_spaces_entail_wit_3.
Axiom proof_of_string_count_spaces_return_wit_1 : string_count_spaces_return_wit_1.
Axiom proof_of_string_count_spaces_partial_solve_wit_1 : string_count_spaces_partial_solve_wit_1.
Axiom proof_of_string_count_spaces_partial_solve_wit_2 : string_count_spaces_partial_solve_wit_2.

End VC_Correct.
