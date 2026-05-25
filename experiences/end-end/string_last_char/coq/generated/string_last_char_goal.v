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

(*----- Function string_last_char -----*)

Definition string_last_char_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (1 <= n) |] 
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

Definition string_last_char_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_last_char_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_last_char_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_last_char_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_last_char_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_last_char_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_last_char_entail_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_last_char_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (i = (n - 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_last_char_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (i = (n - 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (n - 1 ) l 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_last_char_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + ((i + 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i + 1 ) 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_last_char_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (i = (n - 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (i = (n - 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_last_char_safety_wit_1 : string_last_char_safety_wit_1.
Axiom proof_of_string_last_char_safety_wit_2 : string_last_char_safety_wit_2.
Axiom proof_of_string_last_char_safety_wit_3 : string_last_char_safety_wit_3.
Axiom proof_of_string_last_char_safety_wit_4 : string_last_char_safety_wit_4.
Axiom proof_of_string_last_char_safety_wit_5 : string_last_char_safety_wit_5.
Axiom proof_of_string_last_char_safety_wit_6 : string_last_char_safety_wit_6.
Axiom proof_of_string_last_char_entail_wit_1 : string_last_char_entail_wit_1.
Axiom proof_of_string_last_char_entail_wit_2 : string_last_char_entail_wit_2.
Axiom proof_of_string_last_char_entail_wit_3 : string_last_char_entail_wit_3.
Axiom proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Axiom proof_of_string_last_char_partial_solve_wit_1 : string_last_char_partial_solve_wit_1.
Axiom proof_of_string_last_char_partial_solve_wit_2 : string_last_char_partial_solve_wit_2.

End VC_Correct.
