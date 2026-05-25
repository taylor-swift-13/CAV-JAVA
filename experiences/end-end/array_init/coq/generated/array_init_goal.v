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

(*----- Function array_init -----*)

Definition array_init_safety_wit_1 := 
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

Definition array_init_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_init_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) (lr': (@list Z)) ,
  [| ((Zlength (lr')) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 lr' 0) = 0)) |] 
  &&  [| forall (k_4: Z) , ((((i + 1 ) <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr' 0) = (Znth k_4 l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lr' )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_init_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_init_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i: Z) (lr': (@list Z)) ,
  [| ((Zlength (lr')) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 lr' 0) = 0)) |] 
  &&  [| forall (k_4: Z) , ((((i + 1 ) <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr' 0) = (Znth k_4 l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr_2 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr' )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((i + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_init_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k lr_2 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr_2 )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = 0)) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_init_partial_solve_wit_1_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lr )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |]
.

Definition array_init_partial_solve_wit_1_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_init_partial_solve_wit_1 := array_init_partial_solve_wit_1_pure -> array_init_partial_solve_wit_1_aux.

Definition array_init_partial_solve_wit_2_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |]
.

Definition array_init_partial_solve_wit_2_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
.

Definition array_init_partial_solve_wit_2 := array_init_partial_solve_wit_2_pure -> array_init_partial_solve_wit_2_aux.

Definition array_init_which_implies_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k lr 0) = 0)) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr 0) = (Znth k_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lr )
|--
  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
.

Definition array_init_which_implies_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 lr 0) = 0)) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lr 0) = (Znth k_4 l 0))) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre lr )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
|--
  EX (lr': (@list Z)) ,
  [| ((Zlength (lr')) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k lr' 0) = 0)) |] 
  &&  [| forall (k_2: Z) , ((((i + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lr' 0) = (Znth k_2 l 0))) |]
  &&  (IntArray.full a_pre n_pre lr' )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_init_safety_wit_1 : array_init_safety_wit_1.
Axiom proof_of_array_init_safety_wit_2 : array_init_safety_wit_2.
Axiom proof_of_array_init_safety_wit_3 : array_init_safety_wit_3.
Axiom proof_of_array_init_entail_wit_1 : array_init_entail_wit_1.
Axiom proof_of_array_init_entail_wit_2 : array_init_entail_wit_2.
Axiom proof_of_array_init_return_wit_1 : array_init_return_wit_1.
Axiom proof_of_array_init_partial_solve_wit_1_pure : array_init_partial_solve_wit_1_pure.
Axiom proof_of_array_init_partial_solve_wit_1 : array_init_partial_solve_wit_1.
Axiom proof_of_array_init_partial_solve_wit_2_pure : array_init_partial_solve_wit_2_pure.
Axiom proof_of_array_init_partial_solve_wit_2 : array_init_partial_solve_wit_2.
Axiom proof_of_array_init_which_implies_wit_1 : array_init_which_implies_wit_1.
Axiom proof_of_array_init_which_implies_wit_2 : array_init_which_implies_wit_2.

End VC_Correct.
