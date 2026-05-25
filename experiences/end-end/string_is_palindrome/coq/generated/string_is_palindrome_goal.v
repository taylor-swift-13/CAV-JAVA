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

(*----- Function string_is_palindrome -----*)

Definition string_is_palindrome_safety_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_is_palindrome_safety_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre l )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition string_is_palindrome_safety_wit_3 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_is_palindrome_safety_wit_4 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| ((Znth left l 0) <> (Znth right l 0)) |] 
  &&  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_is_palindrome_safety_wit_5 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| ((Znth left l 0) = (Znth right l 0)) |] 
  &&  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((left + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (left + 1 )) |]
.

Definition string_is_palindrome_safety_wit_6 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| ((Znth left l 0) = (Znth right l 0)) |] 
  &&  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> (left + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((right - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (right - 1 )) |]
.

Definition string_is_palindrome_safety_wit_7 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_is_palindrome_entail_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre - 1 ) = ((n_pre - 1 ) - 0 )) |] 
  &&  [| ((-1) <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
.

Definition string_is_palindrome_entail_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| ((Znth left l 0) = (Znth right l 0)) |] 
  &&  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  [| (0 <= (left + 1 )) |] 
  &&  [| ((left + 1 ) <= n_pre) |] 
  &&  [| ((right - 1 ) = ((n_pre - 1 ) - (left + 1 ) )) |] 
  &&  [| ((-1) <= (right - 1 )) |] 
  &&  [| ((right - 1 ) < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (left + 1 ))) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
.

Definition string_is_palindrome_return_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| ((Znth left l 0) <> (Znth right l 0)) |] 
  &&  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  (EX (i: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Znth i l 0) <> (Znth ((n_pre - 1 ) - i ) l 0)) |]
  &&  (CharArray.full s_pre n_pre l ))
  ||
  ([| (0 = 1) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) = (Znth ((n_pre - 1 ) - i_2 ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l ))
.

Definition string_is_palindrome_return_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  (EX (i: Z) ,
  [| (1 = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Znth i l 0) <> (Znth ((n_pre - 1 ) - i ) l 0)) |]
  &&  (CharArray.full s_pre n_pre l ))
  ||
  ([| (1 = 1) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) = (Znth ((n_pre - 1 ) - i_2 ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l ))
.

Definition string_is_palindrome_partial_solve_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (((s_pre + (left * sizeof(CHAR) ) )) # Char  |-> (Znth left l 0))
  **  (CharArray.missing_i s_pre left 0 n_pre l )
.

Definition string_is_palindrome_partial_solve_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (CharArray.full s_pre n_pre l )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| (right = ((n_pre - 1 ) - left )) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < left)) -> ((Znth k l 0) = (Znth ((n_pre - 1 ) - k ) l 0))) |]
  &&  (((s_pre + (right * sizeof(CHAR) ) )) # Char  |-> (Znth right l 0))
  **  (CharArray.missing_i s_pre right 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_is_palindrome_safety_wit_1 : string_is_palindrome_safety_wit_1.
Axiom proof_of_string_is_palindrome_safety_wit_2 : string_is_palindrome_safety_wit_2.
Axiom proof_of_string_is_palindrome_safety_wit_3 : string_is_palindrome_safety_wit_3.
Axiom proof_of_string_is_palindrome_safety_wit_4 : string_is_palindrome_safety_wit_4.
Axiom proof_of_string_is_palindrome_safety_wit_5 : string_is_palindrome_safety_wit_5.
Axiom proof_of_string_is_palindrome_safety_wit_6 : string_is_palindrome_safety_wit_6.
Axiom proof_of_string_is_palindrome_safety_wit_7 : string_is_palindrome_safety_wit_7.
Axiom proof_of_string_is_palindrome_entail_wit_1 : string_is_palindrome_entail_wit_1.
Axiom proof_of_string_is_palindrome_entail_wit_2 : string_is_palindrome_entail_wit_2.
Axiom proof_of_string_is_palindrome_return_wit_1 : string_is_palindrome_return_wit_1.
Axiom proof_of_string_is_palindrome_return_wit_2 : string_is_palindrome_return_wit_2.
Axiom proof_of_string_is_palindrome_partial_solve_wit_1 : string_is_palindrome_partial_solve_wit_1.
Axiom proof_of_string_is_palindrome_partial_solve_wit_2 : string_is_palindrome_partial_solve_wit_2.

End VC_Correct.
