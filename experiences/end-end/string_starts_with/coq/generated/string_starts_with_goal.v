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

(*----- Function string_starts_with -----*)

Definition string_starts_with_safety_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_starts_with_safety_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_starts_with_safety_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_starts_with_return_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = c_pre) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 < n) |] 
  &&  [| ((Znth 0 l 0) <> c_pre) |] 
  &&  [| (1 = 0) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 < n) |] 
  &&  [| ((Znth 0 l 0) = c_pre) |] 
  &&  [| (1 = 1) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (n = 0) |] 
  &&  [| (c_pre <> 0) |] 
  &&  [| (1 = 0) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (n = 0) |] 
  &&  [| (c_pre = 0) |] 
  &&  [| (1 = 1) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition string_starts_with_return_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> c_pre) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 < n) |] 
  &&  [| ((Znth 0 l 0) <> c_pre) |] 
  &&  [| (0 = 0) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 < n) |] 
  &&  [| ((Znth 0 l 0) = c_pre) |] 
  &&  [| (0 = 1) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (n = 0) |] 
  &&  [| (c_pre <> 0) |] 
  &&  [| (0 = 0) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (n = 0) |] 
  &&  [| (c_pre = 0) |] 
  &&  [| (0 = 1) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition string_starts_with_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (0 * sizeof(CHAR) ) )) # Char  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre 0 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_starts_with_safety_wit_1 : string_starts_with_safety_wit_1.
Axiom proof_of_string_starts_with_safety_wit_2 : string_starts_with_safety_wit_2.
Axiom proof_of_string_starts_with_safety_wit_3 : string_starts_with_safety_wit_3.
Axiom proof_of_string_starts_with_return_wit_1 : string_starts_with_return_wit_1.
Axiom proof_of_string_starts_with_return_wit_2 : string_starts_with_return_wit_2.
Axiom proof_of_string_starts_with_partial_solve_wit_1 : string_starts_with_partial_solve_wit_1.

End VC_Correct.
