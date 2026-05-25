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

(*----- Function string_replace_char -----*)

Definition string_replace_char_safety_wit_1 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "new_c" ) )) # Char  |-> new_c_pre)
  **  ((( &( "old_c" ) )) # Char  |-> old_c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_replace_char_safety_wit_2 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "old_c" ) )) # Char  |-> old_c_pre)
  **  ((( &( "new_c" ) )) # Char  |-> new_c_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_replace_char_safety_wit_3 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "old_c" ) )) # Char  |-> old_c_pre)
  **  ((( &( "new_c" ) )) # Char  |-> new_c_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_replace_char_safety_wit_4 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) (l2)) 0) <> old_c_pre) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "old_c" ) )) # Char  |-> old_c_pre)
  **  ((( &( "new_c" ) )) # Char  |-> new_c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_replace_char_safety_wit_5 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) = old_c_pre) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (replace_Znth (i) (new_c_pre) ((app (l1) (l2)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "old_c" ) )) # Char  |-> old_c_pre)
  **  ((( &( "new_c" ) )) # Char  |-> new_c_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_replace_char_entail_wit_1 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - 0 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < 0)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < 0)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - 0 ))) -> ((Znth t_3 l2 0) = (Znth (0 + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - 0 ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
.

Definition string_replace_char_entail_wit_2_1 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app (l1_2) (l2_2)) 0) = old_c_pre) |] 
  &&  [| ((Znth i (app (l1_2) (l2_2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1_2 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1_2 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1_2 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2_2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2_2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (replace_Znth (i) (new_c_pre) ((app (l1_2) (l2_2)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - (i + 1 ) )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < (i + 1 ))) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (i + 1 ))) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - (i + 1 ) ))) -> ((Znth t_3 l2 0) = (Znth ((i + 1 ) + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - (i + 1 ) ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
.

Definition string_replace_char_entail_wit_2_2 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1_2) (l2_2)) 0) <> old_c_pre) |] 
  &&  [| ((Znth i (app (l1_2) (l2_2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1_2 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1_2 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1_2 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2_2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2_2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1_2) (l2_2)) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - (i + 1 ) )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < (i + 1 ))) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (i + 1 ))) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - (i + 1 ) ))) -> ((Znth t_3 l2 0) = (Znth ((i + 1 ) + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - (i + 1 ) ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
.

Definition string_replace_char_return_wit_1 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| ((Znth i_2 (app (l1) (l2)) 0) = 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i_2 )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i_2)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i_2)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i_2 ))) -> ((Znth t_3 l2 0) = (Znth (i_2 + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i_2 ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((((Znth i l 0) = old_c_pre) -> ((Znth i lr 0) = new_c_pre)) /\ (((Znth i l 0) <> old_c_pre) -> ((Znth i lr 0) = (Znth i l 0))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k lr 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (lr) ((cons (0) (nil)))) )
.

Definition string_replace_char_partial_solve_wit_1 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) (l2)) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l1) (l2)) )
.

Definition string_replace_char_partial_solve_wit_2 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) (l2)) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l1) (l2)) )
.

Definition string_replace_char_partial_solve_wit_3 := 
forall (new_c_pre: Z) (old_c_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) (l2)) 0) = old_c_pre) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) = old_c_pre) |] 
  &&  [| ((Znth i (app (l1) (l2)) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ((((Znth t l 0) = old_c_pre) -> ((Znth t l1 0) = new_c_pre)) /\ (((Znth t l 0) <> old_c_pre) -> ((Znth t l1 0) = (Znth t l 0))))) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ((Znth t_2 l1 0) <> 0)) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < (n - i ))) -> ((Znth t_3 l2 0) = (Znth (i + t_3 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (new_c_pre <> 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l1) (l2)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_replace_char_safety_wit_1 : string_replace_char_safety_wit_1.
Axiom proof_of_string_replace_char_safety_wit_2 : string_replace_char_safety_wit_2.
Axiom proof_of_string_replace_char_safety_wit_3 : string_replace_char_safety_wit_3.
Axiom proof_of_string_replace_char_safety_wit_4 : string_replace_char_safety_wit_4.
Axiom proof_of_string_replace_char_safety_wit_5 : string_replace_char_safety_wit_5.
Axiom proof_of_string_replace_char_entail_wit_1 : string_replace_char_entail_wit_1.
Axiom proof_of_string_replace_char_entail_wit_2_1 : string_replace_char_entail_wit_2_1.
Axiom proof_of_string_replace_char_entail_wit_2_2 : string_replace_char_entail_wit_2_2.
Axiom proof_of_string_replace_char_return_wit_1 : string_replace_char_return_wit_1.
Axiom proof_of_string_replace_char_partial_solve_wit_1 : string_replace_char_partial_solve_wit_1.
Axiom proof_of_string_replace_char_partial_solve_wit_2 : string_replace_char_partial_solve_wit_2.
Axiom proof_of_string_replace_char_partial_solve_wit_3 : string_replace_char_partial_solve_wit_3.

End VC_Correct.
