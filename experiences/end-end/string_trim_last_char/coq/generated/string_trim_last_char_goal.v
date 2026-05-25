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

(*----- Function string_trim_last_char -----*)

Definition string_trim_last_char_safety_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_trim_last_char_safety_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition string_trim_last_char_safety_wit_3 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_trim_last_char_safety_wit_4 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_trim_last_char_return_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| (n_pre = 0) |] 
  &&  [| (lr = (app (l) ((cons (0) (nil))))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr ))
  ||
  (EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < (n_pre - 1 ))) -> ((Znth i lr 0) = (Znth i l 0))) |] 
  &&  [| ((Znth (n_pre - 1 ) lr 0) = 0) |] 
  &&  [| ((Znth n_pre lr 0) = 0) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr ))
.

Definition string_trim_last_char_return_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (replace_Znth ((n_pre - 1 )) (0) ((app (l) ((cons (0) (nil)))))) )
|--
  (EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| (n_pre = 0) |] 
  &&  [| (lr = (app (l) ((cons (0) (nil))))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr ))
  ||
  (EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < (n_pre - 1 ))) -> ((Znth i lr 0) = (Znth i l 0))) |] 
  &&  [| ((Znth (n_pre - 1 ) lr 0) = 0) |] 
  &&  [| ((Znth n_pre lr 0) = 0) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr ))
.

Definition string_trim_last_char_partial_solve_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + ((n_pre - 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i s_pre (n_pre - 1 ) 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_trim_last_char_safety_wit_1 : string_trim_last_char_safety_wit_1.
Axiom proof_of_string_trim_last_char_safety_wit_2 : string_trim_last_char_safety_wit_2.
Axiom proof_of_string_trim_last_char_safety_wit_3 : string_trim_last_char_safety_wit_3.
Axiom proof_of_string_trim_last_char_safety_wit_4 : string_trim_last_char_safety_wit_4.
Axiom proof_of_string_trim_last_char_return_wit_1 : string_trim_last_char_return_wit_1.
Axiom proof_of_string_trim_last_char_return_wit_2 : string_trim_last_char_return_wit_2.
Axiom proof_of_string_trim_last_char_partial_solve_wit_1 : string_trim_last_char_partial_solve_wit_1.

End VC_Correct.
