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
Require Import tribonacci.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function tribonacci -----*)

Definition tribonacci_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition tribonacci_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition tribonacci_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition tribonacci_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition tribonacci_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition tribonacci_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition tribonacci_safety_wit_7 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition tribonacci_safety_wit_8 := 
forall (n_pre: Z) ,
  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition tribonacci_safety_wit_9 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (tribonacci_z ((i - 3 )))) |] 
  &&  [| (b = (tribonacci_z ((i - 2 )))) |] 
  &&  [| (c = (tribonacci_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |->_)
|--
  [| (((a + b ) + c ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a + b ) + c )) |]
.

Definition tribonacci_safety_wit_10 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (tribonacci_z ((i - 3 )))) |] 
  &&  [| (b = (tribonacci_z ((i - 2 )))) |] 
  &&  [| (c = (tribonacci_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |->_)
|--
  [| ((a + b ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a + b )) |]
.

Definition tribonacci_safety_wit_11 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (tribonacci_z ((i - 3 )))) |] 
  &&  [| (b = (tribonacci_z ((i - 2 )))) |] 
  &&  [| (c = (tribonacci_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> c)
  **  ((( &( "c" ) )) # Int  |-> ((a + b ) + c ))
  **  ((( &( "d" ) )) # Int  |-> ((a + b ) + c ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition tribonacci_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  emp
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= 3) |] 
  &&  [| (3 <= (n_pre + 1 )) |] 
  &&  [| (0 = (tribonacci_z ((3 - 3 )))) |] 
  &&  [| (1 = (tribonacci_z ((3 - 2 )))) |] 
  &&  [| (1 = (tribonacci_z ((3 - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  emp
.

Definition tribonacci_entail_wit_2 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (tribonacci_z ((i - 3 )))) |] 
  &&  [| (b = (tribonacci_z ((i - 2 )))) |] 
  &&  [| (c = (tribonacci_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |-> ((a + b ) + c ))
|--
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (b = (tribonacci_z (((i + 1 ) - 3 )))) |] 
  &&  [| (c = (tribonacci_z (((i + 1 ) - 2 )))) |] 
  &&  [| (((a + b ) + c ) = (tribonacci_z (((i + 1 ) - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  ((( &( "d" ) )) # Int  |->_)
.

Definition tribonacci_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  emp
|--
  [| (0 = (tribonacci_z (n_pre))) |]
  &&  emp
.

Definition tribonacci_return_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  emp
|--
  [| (1 = (tribonacci_z (n_pre))) |]
  &&  emp
.

Definition tribonacci_return_wit_3 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= 37) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (tribonacci_z ((i - 3 )))) |] 
  &&  [| (b = (tribonacci_z ((i - 2 )))) |] 
  &&  [| (c = (tribonacci_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 37) |]
  &&  emp
|--
  [| (c = (tribonacci_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_tribonacci_safety_wit_1 : tribonacci_safety_wit_1.
Axiom proof_of_tribonacci_safety_wit_2 : tribonacci_safety_wit_2.
Axiom proof_of_tribonacci_safety_wit_3 : tribonacci_safety_wit_3.
Axiom proof_of_tribonacci_safety_wit_4 : tribonacci_safety_wit_4.
Axiom proof_of_tribonacci_safety_wit_5 : tribonacci_safety_wit_5.
Axiom proof_of_tribonacci_safety_wit_6 : tribonacci_safety_wit_6.
Axiom proof_of_tribonacci_safety_wit_7 : tribonacci_safety_wit_7.
Axiom proof_of_tribonacci_safety_wit_8 : tribonacci_safety_wit_8.
Axiom proof_of_tribonacci_safety_wit_9 : tribonacci_safety_wit_9.
Axiom proof_of_tribonacci_safety_wit_10 : tribonacci_safety_wit_10.
Axiom proof_of_tribonacci_safety_wit_11 : tribonacci_safety_wit_11.
Axiom proof_of_tribonacci_entail_wit_1 : tribonacci_entail_wit_1.
Axiom proof_of_tribonacci_entail_wit_2 : tribonacci_entail_wit_2.
Axiom proof_of_tribonacci_return_wit_1 : tribonacci_return_wit_1.
Axiom proof_of_tribonacci_return_wit_2 : tribonacci_return_wit_2.
Axiom proof_of_tribonacci_return_wit_3 : tribonacci_return_wit_3.

End VC_Correct.
