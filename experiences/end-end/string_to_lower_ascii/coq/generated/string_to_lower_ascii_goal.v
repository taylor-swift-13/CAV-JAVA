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

(*----- Function string_to_lower_ascii -----*)

Definition string_to_lower_ascii_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
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

Definition string_to_lower_ascii_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((((0 <= t) /\ (t < i)) /\ (65 <= (Znth t l 0))) /\ ((Znth t l 0) <= 90)) -> ((Znth t l1 0) = ((Znth t l 0) + 32 ))) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < i)) /\ (((Znth t_2 l 0) < 65) \/ (90 < (Znth t_2 l 0)))) -> ((Znth t_2 l1 0) = (Znth t_2 l 0))) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < i)) -> ((Znth t_3 l1 0) <> 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n - i ))) -> ((Znth t_4 l2 0) = (Znth (i + t_4 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_to_lower_ascii_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - i )) |] 
  &&  [| forall (t: Z) , (((((0 <= t) /\ (t < i)) /\ (65 <= (Znth t l 0))) /\ ((Znth t l 0) <= 90)) -> ((Znth t l1 0) = ((Znth t l 0) + 32 ))) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < i)) /\ (((Znth t_2 l 0) < 65) \/ (90 < (Znth t_2 l 0)))) -> ((Znth t_2 l1 0) = (Znth t_2 l 0))) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < i)) -> ((Znth t_3 l1 0) <> 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n - i ))) -> ((Znth t_4 l2 0) = (Znth (i + t_4 ) l 0))) |] 
  &&  [| ((Znth (n - i ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
|--
  [| False |]
.

Definition string_to_lower_ascii_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = ((n + 1 ) - 0 )) |] 
  &&  [| forall (t: Z) , (((((0 <= t) /\ (t < 0)) /\ (65 <= (Znth t l 0))) /\ ((Znth t l 0) <= 90)) -> ((Znth t l1 0) = ((Znth t l 0) + 32 ))) |] 
  &&  [| forall (t_2: Z) , ((((0 <= t_2) /\ (t_2 < 0)) /\ (((Znth t_2 l 0) < 65) \/ (90 < (Znth t_2 l 0)))) -> ((Znth t_2 l1 0) = (Znth t_2 l 0))) |] 
  &&  [| forall (t_3: Z) , (((0 <= t_3) /\ (t_3 < 0)) -> ((Znth t_3 l1 0) <> 0)) |] 
  &&  [| forall (t_4: Z) , (((0 <= t_4) /\ (t_4 < (n - 0 ))) -> ((Znth t_4 l2 0) = (Znth (0 + t_4 ) l 0))) |] 
  &&  [| ((Znth (n - 0 ) l2 0) = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l1) (l2)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_to_lower_ascii_safety_wit_1 : string_to_lower_ascii_safety_wit_1.
Axiom proof_of_string_to_lower_ascii_safety_wit_2 : string_to_lower_ascii_safety_wit_2.
Axiom proof_of_string_to_lower_ascii_safety_wit_3 : string_to_lower_ascii_safety_wit_3.
Axiom proof_of_string_to_lower_ascii_entail_wit_1 : string_to_lower_ascii_entail_wit_1.

End VC_Correct.
