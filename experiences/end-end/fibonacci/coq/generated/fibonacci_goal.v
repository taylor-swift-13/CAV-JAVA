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
Require Import fibonacci.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function fibonacci -----*)

Definition fibonacci_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fibonacci_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fibonacci_safety_wit_6 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_z ((i - 2 )))) |] 
  &&  [| (b = (fib_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |->_)
|--
  [| ((a + b ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a + b )) |]
.

Definition fibonacci_safety_wit_7 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_z ((i - 2 )))) |] 
  &&  [| (b = (fib_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> (a + b ))
  **  ((( &( "c" ) )) # Int  |-> (a + b ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fibonacci_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= (n_pre + 1 )) |] 
  &&  [| (0 = (fib_z ((2 - 2 )))) |] 
  &&  [| (1 = (fib_z ((2 - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  emp
.

Definition fibonacci_entail_wit_2 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_z ((i - 2 )))) |] 
  &&  [| (b = (fib_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "c" ) )) # Int  |-> (a + b ))
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (b = (fib_z (((i + 1 ) - 2 )))) |] 
  &&  [| ((a + b ) = (fib_z (((i + 1 ) - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  ((( &( "c" ) )) # Int  |->_)
.

Definition fibonacci_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  emp
|--
  [| (0 = (fib_z (n_pre))) |]
  &&  emp
.

Definition fibonacci_return_wit_2 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_z ((i - 2 )))) |] 
  &&  [| (b = (fib_z ((i - 1 )))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46) |]
  &&  emp
|--
  [| (b = (fib_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_fibonacci_safety_wit_1 : fibonacci_safety_wit_1.
Axiom proof_of_fibonacci_safety_wit_2 : fibonacci_safety_wit_2.
Axiom proof_of_fibonacci_safety_wit_3 : fibonacci_safety_wit_3.
Axiom proof_of_fibonacci_safety_wit_4 : fibonacci_safety_wit_4.
Axiom proof_of_fibonacci_safety_wit_5 : fibonacci_safety_wit_5.
Axiom proof_of_fibonacci_safety_wit_6 : fibonacci_safety_wit_6.
Axiom proof_of_fibonacci_safety_wit_7 : fibonacci_safety_wit_7.
Axiom proof_of_fibonacci_entail_wit_1 : fibonacci_entail_wit_1.
Axiom proof_of_fibonacci_entail_wit_2 : fibonacci_entail_wit_2.
Axiom proof_of_fibonacci_return_wit_1 : fibonacci_return_wit_1.
Axiom proof_of_fibonacci_return_wit_2 : fibonacci_return_wit_2.

End VC_Correct.
