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
Require Import string_remove_char_to_output.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_remove_char_to_output -----*)

Definition string_remove_char_to_output_safety_wit_1 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_remove_char_to_output_safety_wit_2 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_remove_char_to_output_safety_wit_3 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_remove_char_to_output_safety_wit_4 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_remove_char_to_output_safety_wit_5 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition string_remove_char_to_output_safety_wit_6 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_remove_char_to_output_safety_wit_7 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_remove_char_to_output_safety_wit_8 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (x: Z) (t: (@list Z)) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| (j <= n) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t)) = (n - j )) |]
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (x) (nil))))) (t)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_remove_char_to_output_entail_wit_1 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  EX (d1: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| (0 = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - 0 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_entail_wit_2_1 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1_2) (c_pre))))) |] 
  &&  [| ((Zlength (d1_2)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_remove_char_to_output_spec (l1_2) (c_pre))) (d1_2)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (d1: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((j + 1 ) = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - (j + 1 ) )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_entail_wit_2_2 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1_2) (c_pre))))) |] 
  &&  [| ((Zlength (d1_2)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1_2) (c_pre))) (d1_2)) )
|--
  EX (d1: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_entail_wit_3 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  EX (x: Z)  (t: (@list Z)) ,
  [| (0 <= j) |] 
  &&  [| (j <= n) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t)) = (n - j )) |]
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (x) (nil))))) (t)) )
.

Definition string_remove_char_to_output_return_wit_1 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (x: Z) (t_2: (@list Z)) (j: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= n) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t_2)) = (n - j )) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (0) ((app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (x) (nil))))) (t_2)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (t: (@list Z)) ,
  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t)) = (n - (Zlength ((string_remove_char_to_output_spec (l) (c_pre)))) )) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (0) (nil))))) (t)) )
.

Definition string_remove_char_to_output_partial_solve_wit_1 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_partial_solve_wit_2 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_partial_solve_wit_3 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
.

Definition string_remove_char_to_output_partial_solve_wit_4 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (d1: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l1) (c_pre))))) |] 
  &&  [| ((Zlength (d1)) = ((n + 1 ) - j )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((out_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out_pre j 0 (n + 1 ) (app ((string_remove_char_to_output_spec (l1) (c_pre))) (d1)) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_remove_char_to_output_partial_solve_wit_5 := 
forall (c_pre: Z) (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (x: Z) (t: (@list Z)) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| (j <= n) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t)) = (n - j )) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (x) (nil))))) (t)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= n) |] 
  &&  [| (j = (Zlength ((string_remove_char_to_output_spec (l) (c_pre))))) |] 
  &&  [| ((Zlength (t)) = (n - j )) |]
  &&  (((out_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out_pre j 0 (n + 1 ) (app ((app ((string_remove_char_to_output_spec (l) (c_pre))) ((cons (x) (nil))))) (t)) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_remove_char_to_output_safety_wit_1 : string_remove_char_to_output_safety_wit_1.
Axiom proof_of_string_remove_char_to_output_safety_wit_2 : string_remove_char_to_output_safety_wit_2.
Axiom proof_of_string_remove_char_to_output_safety_wit_3 : string_remove_char_to_output_safety_wit_3.
Axiom proof_of_string_remove_char_to_output_safety_wit_4 : string_remove_char_to_output_safety_wit_4.
Axiom proof_of_string_remove_char_to_output_safety_wit_5 : string_remove_char_to_output_safety_wit_5.
Axiom proof_of_string_remove_char_to_output_safety_wit_6 : string_remove_char_to_output_safety_wit_6.
Axiom proof_of_string_remove_char_to_output_safety_wit_7 : string_remove_char_to_output_safety_wit_7.
Axiom proof_of_string_remove_char_to_output_safety_wit_8 : string_remove_char_to_output_safety_wit_8.
Axiom proof_of_string_remove_char_to_output_entail_wit_1 : string_remove_char_to_output_entail_wit_1.
Axiom proof_of_string_remove_char_to_output_entail_wit_2_1 : string_remove_char_to_output_entail_wit_2_1.
Axiom proof_of_string_remove_char_to_output_entail_wit_2_2 : string_remove_char_to_output_entail_wit_2_2.
Axiom proof_of_string_remove_char_to_output_entail_wit_3 : string_remove_char_to_output_entail_wit_3.
Axiom proof_of_string_remove_char_to_output_return_wit_1 : string_remove_char_to_output_return_wit_1.
Axiom proof_of_string_remove_char_to_output_partial_solve_wit_1 : string_remove_char_to_output_partial_solve_wit_1.
Axiom proof_of_string_remove_char_to_output_partial_solve_wit_2 : string_remove_char_to_output_partial_solve_wit_2.
Axiom proof_of_string_remove_char_to_output_partial_solve_wit_3 : string_remove_char_to_output_partial_solve_wit_3.
Axiom proof_of_string_remove_char_to_output_partial_solve_wit_4 : string_remove_char_to_output_partial_solve_wit_4.
Axiom proof_of_string_remove_char_to_output_partial_solve_wit_5 : string_remove_char_to_output_partial_solve_wit_5.

End VC_Correct.
