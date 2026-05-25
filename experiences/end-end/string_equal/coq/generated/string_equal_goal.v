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

(*----- Function string_equal -----*)

Definition string_equal_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_equal_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_equal_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| False |]
.

Definition string_equal_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition string_equal_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_equal_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= na) |] 
  &&  [| (0 <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= na) |] 
  &&  [| ((i + 1 ) <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((Znth k_5 la 0) = (Znth k_5 lb 0))) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < na)) -> ((Znth k_6 la 0) <> 0)) |] 
  &&  [| forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < nb)) -> ((Znth k_7 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  ([| (0 = 0) |] 
  &&  [| (na <> nb) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < na) |] 
  &&  [| (k < nb) |] 
  &&  [| ((Znth k la 0) <> (Znth k lb 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (0 = 1) |] 
  &&  [| (na = nb) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth k_2 la 0) = (Znth k_2 lb 0))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((Znth k_5 la 0) = (Znth k_5 lb 0))) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < na)) -> ((Znth k_6 la 0) <> 0)) |] 
  &&  [| forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < nb)) -> ((Znth k_7 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  ([| (1 = 0) |] 
  &&  [| (na <> nb) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  (EX (k: Z) ,
  [| (1 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < na) |] 
  &&  [| (k < nb) |] 
  &&  [| ((Znth k la 0) <> (Znth k lb 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (1 = 1) |] 
  &&  [| (na = nb) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth k_2 la 0) = (Znth k_2 lb 0))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((Znth k_5 la 0) = (Znth k_5 lb 0))) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < na)) -> ((Znth k_6 la 0) <> 0)) |] 
  &&  [| forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < nb)) -> ((Znth k_7 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  ([| (0 = 0) |] 
  &&  [| (na <> nb) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < na) |] 
  &&  [| (k < nb) |] 
  &&  [| ((Znth k la 0) <> (Znth k lb 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (0 = 1) |] 
  &&  [| (na = nb) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth k_2 la 0) = (Znth k_2 lb 0))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_return_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((Znth k_5 la 0) = (Znth k_5 lb 0))) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < na)) -> ((Znth k_6 la 0) <> 0)) |] 
  &&  [| forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < nb)) -> ((Znth k_7 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  ([| (0 = 0) |] 
  &&  [| (na <> nb) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < na) |] 
  &&  [| (k < nb) |] 
  &&  [| ((Znth k la 0) <> (Znth k lb 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (0 = 1) |] 
  &&  [| (na = nb) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth k_2 la 0) = (Znth k_2 lb 0))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 la 0) = (Znth k_3 lb 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth k_4 la 0) <> 0)) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < nb)) -> ((Znth k_5 lb 0) <> 0)) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (la)) = na) |] 
  &&  [| ((Zlength (lb)) = nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_equal_safety_wit_1 : string_equal_safety_wit_1.
Axiom proof_of_string_equal_safety_wit_2 : string_equal_safety_wit_2.
Axiom proof_of_string_equal_safety_wit_3 : string_equal_safety_wit_3.
Axiom proof_of_string_equal_safety_wit_4 : string_equal_safety_wit_4.
Axiom proof_of_string_equal_safety_wit_5 : string_equal_safety_wit_5.
Axiom proof_of_string_equal_safety_wit_6 : string_equal_safety_wit_6.
Axiom proof_of_string_equal_safety_wit_7 : string_equal_safety_wit_7.
Axiom proof_of_string_equal_safety_wit_8 : string_equal_safety_wit_8.
Axiom proof_of_string_equal_safety_wit_9 : string_equal_safety_wit_9.
Axiom proof_of_string_equal_safety_wit_10 : string_equal_safety_wit_10.
Axiom proof_of_string_equal_safety_wit_11 : string_equal_safety_wit_11.
Axiom proof_of_string_equal_safety_wit_12 : string_equal_safety_wit_12.
Axiom proof_of_string_equal_safety_wit_13 : string_equal_safety_wit_13.
Axiom proof_of_string_equal_safety_wit_14 : string_equal_safety_wit_14.
Axiom proof_of_string_equal_entail_wit_1 : string_equal_entail_wit_1.
Axiom proof_of_string_equal_entail_wit_2 : string_equal_entail_wit_2.
Axiom proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Axiom proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Axiom proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Axiom proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
Axiom proof_of_string_equal_partial_solve_wit_1 : string_equal_partial_solve_wit_1.
Axiom proof_of_string_equal_partial_solve_wit_2 : string_equal_partial_solve_wit_2.
Axiom proof_of_string_equal_partial_solve_wit_3 : string_equal_partial_solve_wit_3.
Axiom proof_of_string_equal_partial_solve_wit_4 : string_equal_partial_solve_wit_4.
Axiom proof_of_string_equal_partial_solve_wit_5 : string_equal_partial_solve_wit_5.
Axiom proof_of_string_equal_partial_solve_wit_6 : string_equal_partial_solve_wit_6.
Axiom proof_of_string_equal_partial_solve_wit_7 : string_equal_partial_solve_wit_7.

End VC_Correct.
