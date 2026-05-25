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
Require Import string_collapse_spaces.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_collapse_spaces -----*)

Definition string_collapse_spaces_safety_wit_1 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_2 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_3 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "in_space" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_4 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_collapse_spaces_safety_wit_5 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_6 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition string_collapse_spaces_safety_wit_7 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_8 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition string_collapse_spaces_safety_wit_9 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (32) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition string_collapse_spaces_safety_wit_10 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (32) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_collapse_spaces_safety_wit_11 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition string_collapse_spaces_safety_wit_12 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_safety_wit_13 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "in_space" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_collapse_spaces_safety_wit_14 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_collapse_spaces_safety_wit_15 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (32) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "in_space" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_collapse_spaces_safety_wit_16 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "in_space" ) )) # Int  |-> in_space)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_collapse_spaces_entail_wit_1 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (d: (@list Z)) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) d )
|--
  EX (dout: (@list Z))  (lin: (@list Z))  (lrest: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = 0) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (0 = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((0 = 0) /\ (0 < 0)) -> ((Znth (0 - 1 ) l 0) <> 32)) |] 
  &&  [| ((0 = 1) -> ((0 < 0) /\ ((Znth (0 - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_entail_wit_2_1 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout_2: (@list Z)) (lin_2: (@list Z)) (lrest_2: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin_2) (lrest_2))) |] 
  &&  [| ((Zlength (lin_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin_2))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (32) ((app ((string_collapse_spaces_spec (lin_2))) (dout_2)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (dout: (@list Z))  (lin: (@list Z))  (lrest: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((j + 1 ) = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((1 = 0) /\ (0 < (i + 1 ))) -> ((Znth ((i + 1 ) - 1 ) l 0) <> 32)) |] 
  &&  [| ((1 = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_entail_wit_2_2 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout_2: (@list Z)) (lin_2: (@list Z)) (lrest_2: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin_2) (lrest_2))) |] 
  &&  [| ((Zlength (lin_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin_2))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin_2))) (dout_2)) )
|--
  EX (dout: (@list Z))  (lin: (@list Z))  (lrest: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < (i + 1 ))) -> ((Znth ((i + 1 ) - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_entail_wit_2_3 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout_2: (@list Z)) (lin_2: (@list Z)) (lrest_2: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin_2) (lrest_2))) |] 
  &&  [| ((Zlength (lin_2)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin_2))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) ((Znth i (app (l) ((cons (0) (nil)))) 0)) ((app ((string_collapse_spaces_spec (lin_2))) (dout_2)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (dout: (@list Z))  (lin: (@list Z))  (lrest: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((j + 1 ) = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((0 = 0) /\ (0 < (i + 1 ))) -> ((Znth ((i + 1 ) - 1 ) l 0) <> 32)) |] 
  &&  [| ((0 = 1) -> ((0 < (i + 1 )) /\ ((Znth ((i + 1 ) - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_return_wit_1 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full out_pre (n + 1 ) (replace_Znth (j) (0) ((app ((string_collapse_spaces_spec (lin))) (dout)))) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (t: (@list Z)) ,
  [| ((Zlength (t)) = (n - (Zlength ((string_collapse_spaces_spec (l)))) )) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((app ((string_collapse_spaces_spec (l))) ((cons (0) (nil))))) (t)) )
.

Definition string_collapse_spaces_partial_solve_wit_1 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_partial_solve_wit_2 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_partial_solve_wit_3 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| (in_space = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((out_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out_pre j 0 (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_collapse_spaces_partial_solve_wit_4 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
.

Definition string_collapse_spaces_partial_solve_wit_5 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((out_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out_pre j 0 (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_collapse_spaces_partial_solve_wit_6 := 
forall (out_pre: Z) (s_pre: Z) (n: Z) (l: (@list Z)) (dout: (@list Z)) (lin: (@list Z)) (lrest: (@list Z)) (in_space: Z) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out_pre (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (0 <= in_space) |] 
  &&  [| (in_space <= 1) |] 
  &&  [| (l = (app (lin) (lrest))) |] 
  &&  [| ((Zlength (lin)) = i) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (j = (Zlength ((string_collapse_spaces_spec (lin))))) |] 
  &&  [| (((in_space = 0) /\ (0 < i)) -> ((Znth (i - 1 ) l 0) <> 32)) |] 
  &&  [| ((in_space = 1) -> ((0 < i) /\ ((Znth (i - 1 ) l 0) = 32))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((out_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out_pre j 0 (n + 1 ) (app ((string_collapse_spaces_spec (lin))) (dout)) )
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_collapse_spaces_safety_wit_1 : string_collapse_spaces_safety_wit_1.
Axiom proof_of_string_collapse_spaces_safety_wit_2 : string_collapse_spaces_safety_wit_2.
Axiom proof_of_string_collapse_spaces_safety_wit_3 : string_collapse_spaces_safety_wit_3.
Axiom proof_of_string_collapse_spaces_safety_wit_4 : string_collapse_spaces_safety_wit_4.
Axiom proof_of_string_collapse_spaces_safety_wit_5 : string_collapse_spaces_safety_wit_5.
Axiom proof_of_string_collapse_spaces_safety_wit_6 : string_collapse_spaces_safety_wit_6.
Axiom proof_of_string_collapse_spaces_safety_wit_7 : string_collapse_spaces_safety_wit_7.
Axiom proof_of_string_collapse_spaces_safety_wit_8 : string_collapse_spaces_safety_wit_8.
Axiom proof_of_string_collapse_spaces_safety_wit_9 : string_collapse_spaces_safety_wit_9.
Axiom proof_of_string_collapse_spaces_safety_wit_10 : string_collapse_spaces_safety_wit_10.
Axiom proof_of_string_collapse_spaces_safety_wit_11 : string_collapse_spaces_safety_wit_11.
Axiom proof_of_string_collapse_spaces_safety_wit_12 : string_collapse_spaces_safety_wit_12.
Axiom proof_of_string_collapse_spaces_safety_wit_13 : string_collapse_spaces_safety_wit_13.
Axiom proof_of_string_collapse_spaces_safety_wit_14 : string_collapse_spaces_safety_wit_14.
Axiom proof_of_string_collapse_spaces_safety_wit_15 : string_collapse_spaces_safety_wit_15.
Axiom proof_of_string_collapse_spaces_safety_wit_16 : string_collapse_spaces_safety_wit_16.
Axiom proof_of_string_collapse_spaces_entail_wit_1 : string_collapse_spaces_entail_wit_1.
Axiom proof_of_string_collapse_spaces_entail_wit_2_1 : string_collapse_spaces_entail_wit_2_1.
Axiom proof_of_string_collapse_spaces_entail_wit_2_2 : string_collapse_spaces_entail_wit_2_2.
Axiom proof_of_string_collapse_spaces_entail_wit_2_3 : string_collapse_spaces_entail_wit_2_3.
Axiom proof_of_string_collapse_spaces_return_wit_1 : string_collapse_spaces_return_wit_1.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_1 : string_collapse_spaces_partial_solve_wit_1.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_2 : string_collapse_spaces_partial_solve_wit_2.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_3 : string_collapse_spaces_partial_solve_wit_3.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_4 : string_collapse_spaces_partial_solve_wit_4.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_5 : string_collapse_spaces_partial_solve_wit_5.
Axiom proof_of_string_collapse_spaces_partial_solve_wit_6 : string_collapse_spaces_partial_solve_wit_6.

End VC_Correct.
