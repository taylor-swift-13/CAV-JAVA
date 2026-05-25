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
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function array_replace_negative_zero -----*)

Definition array_replace_negative_zero_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_replace_negative_zero_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_replace_negative_zero_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| ((Znth i lc 0) < 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_replace_negative_zero_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| ((Znth i lc 0) >= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_replace_negative_zero_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| ((Znth i lc 0) < 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) (0) (lc)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_replace_negative_zero_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < 0)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < 0)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_replace_negative_zero_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (i: Z) ,
  [| ((Znth i lc_2 0) < 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc_2 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc_2 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) (0) (lc_2)) )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , ((((i + 1 ) <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_replace_negative_zero_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (i: Z) ,
  [| ((Znth i lc_2 0) >= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc_2 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc_2 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , ((((i + 1 ) <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_replace_negative_zero_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , ((((0 <= k_3) /\ (k_3 < i)) /\ ((Znth k_3 l 0) < 0)) -> ((Znth k_3 lc_2 0) = 0)) |] 
  &&  [| forall (k_4: Z) , ((((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 l 0) >= 0)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| forall (k_5: Z) , (((i <= k_5) /\ (k_5 < n_pre)) -> ((Znth k_5 lc_2 0) = (Znth k_5 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  EX (lc: (@list Z)) ,
  [| (i = n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < n_pre)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < n_pre)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_replace_negative_zero_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i_2: Z) ,
  [| (i_2 = n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < n_pre)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < n_pre)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (l0: (@list Z)) ,
  [| ((Zlength (l0)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((Znth i l 0) < 0) -> ((Znth i l0 0) = 0)) /\ (((Znth i l 0) >= 0) -> ((Znth i l0 0) = (Znth i l 0))))) |]
  &&  (IntArray.full a_pre n_pre l0 )
.

Definition array_replace_negative_zero_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lc 0))
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition array_replace_negative_zero_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (i: Z) ,
  [| ((Znth i lc 0) < 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) < 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k l 0) < 0)) -> ((Znth k lc 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 l 0) >= 0)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lc 0) = (Znth k_3 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_replace_negative_zero_safety_wit_1 : array_replace_negative_zero_safety_wit_1.
Axiom proof_of_array_replace_negative_zero_safety_wit_2 : array_replace_negative_zero_safety_wit_2.
Axiom proof_of_array_replace_negative_zero_safety_wit_3 : array_replace_negative_zero_safety_wit_3.
Axiom proof_of_array_replace_negative_zero_safety_wit_4 : array_replace_negative_zero_safety_wit_4.
Axiom proof_of_array_replace_negative_zero_safety_wit_5 : array_replace_negative_zero_safety_wit_5.
Axiom proof_of_array_replace_negative_zero_entail_wit_1 : array_replace_negative_zero_entail_wit_1.
Axiom proof_of_array_replace_negative_zero_entail_wit_2_1 : array_replace_negative_zero_entail_wit_2_1.
Axiom proof_of_array_replace_negative_zero_entail_wit_2_2 : array_replace_negative_zero_entail_wit_2_2.
Axiom proof_of_array_replace_negative_zero_entail_wit_3 : array_replace_negative_zero_entail_wit_3.
Axiom proof_of_array_replace_negative_zero_return_wit_1 : array_replace_negative_zero_return_wit_1.
Axiom proof_of_array_replace_negative_zero_partial_solve_wit_1 : array_replace_negative_zero_partial_solve_wit_1.
Axiom proof_of_array_replace_negative_zero_partial_solve_wit_2 : array_replace_negative_zero_partial_solve_wit_2.

End VC_Correct.
