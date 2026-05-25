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
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_min -----*)

Definition array_min_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_min_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_min_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx: Z) (i: Z) ,
  [| ((Znth i l 0) >= ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_min_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx: Z) (i: Z) ,
  [| ((Znth i l 0) < ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_min_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (idx: Z) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < 1) |] 
  &&  [| ((Znth idx l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < 1)) -> ((Znth 0 l 0) <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_min_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx_2: Z) (i: Z) ,
  [| ((Znth i l 0) < ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx_2) |] 
  &&  [| (idx_2 < i) |] 
  &&  [| ((Znth idx_2 l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (idx: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < (i + 1 )) |] 
  &&  [| ((Znth idx l 0) = (Znth i l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_min_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx_2: Z) (i: Z) ,
  [| ((Znth i l 0) >= ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx_2) |] 
  &&  [| (idx_2 < i) |] 
  &&  [| ((Znth idx_2 l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (idx: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < (i + 1 )) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_min_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx: Z) (i_3: Z) ,
  [| (i_3 >= n_pre) |] 
  &&  [| (1 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i_3) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i_3)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Znth i l 0) = ret) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (ret <= (Znth i_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_min_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_min_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_min_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (idx: Z) (i: Z) ,
  [| ((Znth i l 0) < ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i l 0) < ret) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= idx) |] 
  &&  [| (idx < i) |] 
  &&  [| ((Znth idx l 0) = ret) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> (ret <= (Znth j l 0))) |] 
  &&  [| (1 <= n_pre) |] 
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

Axiom proof_of_array_min_safety_wit_1 : array_min_safety_wit_1.
Axiom proof_of_array_min_safety_wit_2 : array_min_safety_wit_2.
Axiom proof_of_array_min_safety_wit_3 : array_min_safety_wit_3.
Axiom proof_of_array_min_safety_wit_4 : array_min_safety_wit_4.
Axiom proof_of_array_min_entail_wit_1 : array_min_entail_wit_1.
Axiom proof_of_array_min_entail_wit_2_1 : array_min_entail_wit_2_1.
Axiom proof_of_array_min_entail_wit_2_2 : array_min_entail_wit_2_2.
Axiom proof_of_array_min_return_wit_1 : array_min_return_wit_1.
Axiom proof_of_array_min_partial_solve_wit_1 : array_min_partial_solve_wit_1.
Axiom proof_of_array_min_partial_solve_wit_2 : array_min_partial_solve_wit_2.
Axiom proof_of_array_min_partial_solve_wit_3 : array_min_partial_solve_wit_3.

End VC_Correct.
