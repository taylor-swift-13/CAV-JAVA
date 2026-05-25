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
Require Import climb_stairs.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function climb_stairs -----*)

Definition climb_stairs_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition climb_stairs_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre <= 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition climb_stairs_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition climb_stairs_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition climb_stairs_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |-> 1)
  **  ((( &( "prev2" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition climb_stairs_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "prev1" ) )) # Int  |-> 1)
  **  ((( &( "prev2" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition climb_stairs_safety_wit_7 := 
forall (n_pre: Z) (cur: Z) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (prev2 = (climb_stairs_z ((i - 2 )))) |] 
  &&  [| (prev1 = (climb_stairs_z ((i - 1 )))) |] 
  &&  [| ((i = 2) -> (cur = 0)) |] 
  &&  [| ((i > 2) -> (cur = (climb_stairs_z ((i - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  [| ((prev1 + prev2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (prev1 + prev2 )) |]
.

Definition climb_stairs_safety_wit_8 := 
forall (n_pre: Z) (cur: Z) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (prev2 = (climb_stairs_z ((i - 2 )))) |] 
  &&  [| (prev1 = (climb_stairs_z ((i - 1 )))) |] 
  &&  [| ((i = 2) -> (cur = 0)) |] 
  &&  [| ((i > 2) -> (cur = (climb_stairs_z ((i - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "prev1" ) )) # Int  |-> (prev1 + prev2 ))
  **  ((( &( "cur" ) )) # Int  |-> (prev1 + prev2 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition climb_stairs_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= (n_pre + 1 )) |] 
  &&  [| (1 = (climb_stairs_z ((2 - 2 )))) |] 
  &&  [| (1 = (climb_stairs_z ((2 - 1 )))) |] 
  &&  [| ((2 = 2) -> (0 = 0)) |] 
  &&  [| ((2 > 2) -> (0 = (climb_stairs_z ((2 - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
.

Definition climb_stairs_entail_wit_2 := 
forall (n_pre: Z) (cur: Z) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (prev2 = (climb_stairs_z ((i - 2 )))) |] 
  &&  [| (prev1 = (climb_stairs_z ((i - 1 )))) |] 
  &&  [| ((i = 2) -> (cur = 0)) |] 
  &&  [| ((i > 2) -> (cur = (climb_stairs_z ((i - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (prev1 = (climb_stairs_z (((i + 1 ) - 2 )))) |] 
  &&  [| ((prev1 + prev2 ) = (climb_stairs_z (((i + 1 ) - 1 )))) |] 
  &&  [| (((i + 1 ) = 2) -> ((prev1 + prev2 ) = 0)) |] 
  &&  [| (((i + 1 ) > 2) -> ((prev1 + prev2 ) = (climb_stairs_z (((i + 1 ) - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
.

Definition climb_stairs_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <= 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
|--
  [| (1 = (climb_stairs_z (n_pre))) |]
  &&  emp
.

Definition climb_stairs_return_wit_2 := 
forall (n_pre: Z) (cur: Z) (prev1: Z) (prev2: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 45) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (prev2 = (climb_stairs_z ((i - 2 )))) |] 
  &&  [| (prev1 = (climb_stairs_z ((i - 1 )))) |] 
  &&  [| ((i = 2) -> (cur = 0)) |] 
  &&  [| ((i > 2) -> (cur = (climb_stairs_z ((i - 1 ))))) |] 
  &&  [| (n_pre > 1) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 45) |]
  &&  emp
|--
  [| (cur = (climb_stairs_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_climb_stairs_safety_wit_1 : climb_stairs_safety_wit_1.
Axiom proof_of_climb_stairs_safety_wit_2 : climb_stairs_safety_wit_2.
Axiom proof_of_climb_stairs_safety_wit_3 : climb_stairs_safety_wit_3.
Axiom proof_of_climb_stairs_safety_wit_4 : climb_stairs_safety_wit_4.
Axiom proof_of_climb_stairs_safety_wit_5 : climb_stairs_safety_wit_5.
Axiom proof_of_climb_stairs_safety_wit_6 : climb_stairs_safety_wit_6.
Axiom proof_of_climb_stairs_safety_wit_7 : climb_stairs_safety_wit_7.
Axiom proof_of_climb_stairs_safety_wit_8 : climb_stairs_safety_wit_8.
Axiom proof_of_climb_stairs_entail_wit_1 : climb_stairs_entail_wit_1.
Axiom proof_of_climb_stairs_entail_wit_2 : climb_stairs_entail_wit_2.
Axiom proof_of_climb_stairs_return_wit_1 : climb_stairs_return_wit_1.
Axiom proof_of_climb_stairs_return_wit_2 : climb_stairs_return_wit_2.

End VC_Correct.
