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

(*----- Function array_equal -----*)

Definition array_equal_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_equal_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <> (Znth i lb 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_equal_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) = (Znth i lb 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_equal_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (i = n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth j la 0) = (Znth j lb 0))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_equal_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
.

Definition array_equal_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) = (Znth i lb 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
.

Definition array_equal_entail_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 la 0) = (Znth j_2 lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (i = n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth j la 0) = (Znth j lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
.

Definition array_equal_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i_3: Z) ,
  [| ((Znth i_3 la 0) <> (Znth i_3 lb 0)) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i_3)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full b_pre n_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  (EX (i: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Znth i la 0) <> (Znth i lb 0)) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb ))
  ||
  ([| (0 = 1) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 la 0) = (Znth i_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb ))
.

Definition array_equal_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i_3: Z) ,
  [| (i_3 = n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth j la 0) = (Znth j lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  (EX (i: Z) ,
  [| (1 = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((Znth i la 0) <> (Znth i lb 0)) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb ))
  ||
  ([| (1 = 1) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 la 0) = (Znth i_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb ))
.

Definition array_equal_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full b_pre n_pre lb )
.

Definition array_equal_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre n_pre lb )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j la 0) = (Znth j lb 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = n_pre) |]
  &&  (((b_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lb 0))
  **  (IntArray.missing_i b_pre i 0 n_pre lb )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_equal_safety_wit_1 : array_equal_safety_wit_1.
Axiom proof_of_array_equal_safety_wit_2 : array_equal_safety_wit_2.
Axiom proof_of_array_equal_safety_wit_3 : array_equal_safety_wit_3.
Axiom proof_of_array_equal_safety_wit_4 : array_equal_safety_wit_4.
Axiom proof_of_array_equal_entail_wit_1 : array_equal_entail_wit_1.
Axiom proof_of_array_equal_entail_wit_2 : array_equal_entail_wit_2.
Axiom proof_of_array_equal_entail_wit_3 : array_equal_entail_wit_3.
Axiom proof_of_array_equal_return_wit_1 : array_equal_return_wit_1.
Axiom proof_of_array_equal_return_wit_2 : array_equal_return_wit_2.
Axiom proof_of_array_equal_partial_solve_wit_1 : array_equal_partial_solve_wit_1.
Axiom proof_of_array_equal_partial_solve_wit_2 : array_equal_partial_solve_wit_2.

End VC_Correct.
