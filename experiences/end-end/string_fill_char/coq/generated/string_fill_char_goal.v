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

(*----- Function string_fill_char -----*)

Definition string_fill_char_safety_wit_1 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_fill_char_safety_wit_2 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (replace_Znth (i) (c_pre) (lr)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_fill_char_safety_wit_3 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) lr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_fill_char_entail_wit_1 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) l )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr )
.

Definition string_fill_char_entail_wit_2 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr_2)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr_2 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (replace_Znth (i) (c_pre) (lr_2)) )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , ((((i + 1 ) <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr )
.

Definition string_fill_char_return_wit_1 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i_2: Z) ,
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((Zlength (lr_2)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k lr_2 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (replace_Znth (n_pre) (0) (lr_2)) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = c_pre)) |] 
  &&  [| ((Znth n_pre lr 0) = 0) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr )
.

Definition string_fill_char_partial_solve_wit_1 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) lr )
.

Definition string_fill_char_partial_solve_wit_2 := 
forall (s_pre: Z) (c_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) lr )
|--
  [| (0 <= (n_pre + 1 )) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (lr)) = (n_pre + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = c_pre)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = (n_pre + 1 )) |]
  &&  (((s_pre + (n_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i s_pre n_pre 0 (n_pre + 1 ) lr )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_fill_char_safety_wit_1 : string_fill_char_safety_wit_1.
Axiom proof_of_string_fill_char_safety_wit_2 : string_fill_char_safety_wit_2.
Axiom proof_of_string_fill_char_safety_wit_3 : string_fill_char_safety_wit_3.
Axiom proof_of_string_fill_char_entail_wit_1 : string_fill_char_entail_wit_1.
Axiom proof_of_string_fill_char_entail_wit_2 : string_fill_char_entail_wit_2.
Axiom proof_of_string_fill_char_return_wit_1 : string_fill_char_return_wit_1.
Axiom proof_of_string_fill_char_partial_solve_wit_1 : string_fill_char_partial_solve_wit_1.
Axiom proof_of_string_fill_char_partial_solve_wit_2 : string_fill_char_partial_solve_wit_2.

End VC_Correct.
