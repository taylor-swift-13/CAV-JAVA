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

(*----- Function array_last_positive -----*)

Definition array_last_positive_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition array_last_positive_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_last_positive_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ans" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_last_positive_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_last_positive_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| ((Znth i l 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_last_positive_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| ((Znth i l 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ans" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_last_positive_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((-1) <= (-1)) |] 
  &&  [| ((-1) < 0) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (((-1) = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= (-1)) -> (((Znth (-1) l 0) > 0) /\ forall (j_2: Z) , ((((-1) < j_2) /\ (j_2 < 0)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_last_positive_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| ((Znth i l 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((-1) <= i) |] 
  &&  [| (i < (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((i = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= i) -> (((Znth i l 0) > 0) /\ forall (j_2: Z) , (((i < j_2) /\ (j_2 < (i + 1 ))) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_last_positive_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| ((Znth i l 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < (i + 1 )) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < (i + 1 ))) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_last_positive_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < i)) -> ((Znth j_3 l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_4: Z) , (((ans < j_4) /\ (j_4 < i)) -> ((Znth j_4 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i = n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 l 0) <= 0)))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_last_positive_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_3: Z) (ans: Z) ,
  [| (i_3 = n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 l 0) <= 0)))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (0 <= ans) |] 
  &&  [| (ans < n_pre) |] 
  &&  [| ((Znth ans l 0) > 0) |] 
  &&  [| forall (i: Z) , (((ans < i) /\ (i < n_pre)) -> ((Znth i l 0) <= 0)) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (ans = (-1)) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) <= 0)) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_last_positive_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((-1) <= ans) |] 
  &&  [| (ans < i) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((ans = (-1)) -> forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j l 0) <= 0))) |] 
  &&  [| ((0 <= ans) -> (((Znth ans l 0) > 0) /\ forall (j_2: Z) , (((ans < j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) <= 0)))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_last_positive_safety_wit_1 : array_last_positive_safety_wit_1.
Axiom proof_of_array_last_positive_safety_wit_2 : array_last_positive_safety_wit_2.
Axiom proof_of_array_last_positive_safety_wit_3 : array_last_positive_safety_wit_3.
Axiom proof_of_array_last_positive_safety_wit_4 : array_last_positive_safety_wit_4.
Axiom proof_of_array_last_positive_safety_wit_5 : array_last_positive_safety_wit_5.
Axiom proof_of_array_last_positive_safety_wit_6 : array_last_positive_safety_wit_6.
Axiom proof_of_array_last_positive_entail_wit_1 : array_last_positive_entail_wit_1.
Axiom proof_of_array_last_positive_entail_wit_2_1 : array_last_positive_entail_wit_2_1.
Axiom proof_of_array_last_positive_entail_wit_2_2 : array_last_positive_entail_wit_2_2.
Axiom proof_of_array_last_positive_entail_wit_3 : array_last_positive_entail_wit_3.
Axiom proof_of_array_last_positive_return_wit_1 : array_last_positive_return_wit_1.
Axiom proof_of_array_last_positive_partial_solve_wit_1 : array_last_positive_partial_solve_wit_1.

End VC_Correct.
