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
Require Import string_count_words_simple.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_count_words_simple -----*)

Definition string_count_words_simple_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_words_simple_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "in_word" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_words_simple_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "in_word" ) )) # Int  |-> 0)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_words_simple_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_count_words_simple_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_words_simple_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition string_count_words_simple_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_count_words_simple_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition string_count_words_simple_safety_wit_9 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_count_words_simple_safety_wit_10 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> in_word)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_words_simple_safety_wit_11 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "in_word" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_words_simple_safety_wit_12 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "in_word" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_count_words_simple_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (0 = (string_count_words_simple_spec ((sublist (0) (0) (l))))) |] 
  &&  [| ((0 = 0) -> (0 = 0)) |] 
  &&  [| (((0 < 0) /\ (0 = 0)) -> ((Znth (0 - 1 ) l 0) = 32)) |] 
  &&  [| ((0 = 1) -> ((0 < 0) /\ ((Znth (0 - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (((i + 1 ) = 0) -> (0 = 0)) |] 
  &&  [| (((0 < (i + 1 )) /\ (0 = 0)) -> ((Znth ((i + 1 ) - 1 ) l 0) = 32)) |] 
  &&  [| ((0 = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((count + 1 ) = (string_count_words_simple_spec ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (((i + 1 ) = 0) -> (1 = 0)) |] 
  &&  [| (((0 < (i + 1 )) /\ (1 = 0)) -> ((Znth ((i + 1 ) - 1 ) l 0) = 32)) |] 
  &&  [| ((1 = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_entail_wit_2_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (in_word <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (((i + 1 ) = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < (i + 1 )) /\ (in_word = 0)) -> ((Znth ((i + 1 ) - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth k_3 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= count) |] 
  &&  [| (count <= n) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec (l))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (count: Z) (in_word: Z) ,
  [| (0 <= count) |] 
  &&  [| (count <= n) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec (l))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (count = (string_count_words_simple_spec (l))) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_count_words_simple_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (in_word: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
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
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (0 <= in_word) |] 
  &&  [| (in_word <= 1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (count = (string_count_words_simple_spec ((sublist (0) (i) (l))))) |] 
  &&  [| ((i = 0) -> (in_word = 0)) |] 
  &&  [| (((0 < i) /\ (in_word = 0)) -> ((Znth (i - 1 ) l 0) = 32)) |] 
  &&  [| ((in_word = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) <> 32))) |] 
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

Axiom proof_of_string_count_words_simple_safety_wit_1 : string_count_words_simple_safety_wit_1.
Axiom proof_of_string_count_words_simple_safety_wit_2 : string_count_words_simple_safety_wit_2.
Axiom proof_of_string_count_words_simple_safety_wit_3 : string_count_words_simple_safety_wit_3.
Axiom proof_of_string_count_words_simple_safety_wit_4 : string_count_words_simple_safety_wit_4.
Axiom proof_of_string_count_words_simple_safety_wit_5 : string_count_words_simple_safety_wit_5.
Axiom proof_of_string_count_words_simple_safety_wit_6 : string_count_words_simple_safety_wit_6.
Axiom proof_of_string_count_words_simple_safety_wit_7 : string_count_words_simple_safety_wit_7.
Axiom proof_of_string_count_words_simple_safety_wit_8 : string_count_words_simple_safety_wit_8.
Axiom proof_of_string_count_words_simple_safety_wit_9 : string_count_words_simple_safety_wit_9.
Axiom proof_of_string_count_words_simple_safety_wit_10 : string_count_words_simple_safety_wit_10.
Axiom proof_of_string_count_words_simple_safety_wit_11 : string_count_words_simple_safety_wit_11.
Axiom proof_of_string_count_words_simple_safety_wit_12 : string_count_words_simple_safety_wit_12.
Axiom proof_of_string_count_words_simple_entail_wit_1 : string_count_words_simple_entail_wit_1.
Axiom proof_of_string_count_words_simple_entail_wit_2_1 : string_count_words_simple_entail_wit_2_1.
Axiom proof_of_string_count_words_simple_entail_wit_2_2 : string_count_words_simple_entail_wit_2_2.
Axiom proof_of_string_count_words_simple_entail_wit_2_3 : string_count_words_simple_entail_wit_2_3.
Axiom proof_of_string_count_words_simple_entail_wit_3 : string_count_words_simple_entail_wit_3.
Axiom proof_of_string_count_words_simple_return_wit_1 : string_count_words_simple_return_wit_1.
Axiom proof_of_string_count_words_simple_partial_solve_wit_1 : string_count_words_simple_partial_solve_wit_1.
Axiom proof_of_string_count_words_simple_partial_solve_wit_2 : string_count_words_simple_partial_solve_wit_2.

End VC_Correct.
