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
Require Import fibonacci_mod.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function fibonacci_mod -----*)

Definition fibonacci_mod_safety_wit_1 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_mod_safety_wit_2 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((1 <> (INT_MIN)) \/ (mod_pre <> (-1))) |] 
  &&  [| (mod_pre <> 0) |]
.

Definition fibonacci_mod_safety_wit_3 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fibonacci_mod_safety_wit_4 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> (1 % ( mod_pre ) ))
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_mod_safety_wit_5 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> (1 % ( mod_pre ) ))
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibonacci_mod_safety_wit_6 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> (1 % ( mod_pre ) ))
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fibonacci_mod_safety_wit_7 := 
forall (mod_pre: Z) (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_mod_z ((i - 2 )) (mod_pre))) |] 
  &&  [| (b = (fib_mod_z ((i - 1 )) (mod_pre))) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a < mod_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |->_)
|--
  [| (((a + b ) <> (INT_MIN)) \/ (mod_pre <> (-1))) |] 
  &&  [| (mod_pre <> 0) |]
.

Definition fibonacci_mod_safety_wit_8 := 
forall (mod_pre: Z) (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_mod_z ((i - 2 )) (mod_pre))) |] 
  &&  [| (b = (fib_mod_z ((i - 1 )) (mod_pre))) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a < mod_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |->_)
|--
  [| ((a + b ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a + b )) |]
.

Definition fibonacci_mod_safety_wit_9 := 
forall (mod_pre: Z) (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_mod_z ((i - 2 )) (mod_pre))) |] 
  &&  [| (b = (fib_mod_z ((i - 1 )) (mod_pre))) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a < mod_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mod" ) )) # Int  |-> mod_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> ((a + b ) % ( mod_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> ((a + b ) % ( mod_pre ) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fibonacci_mod_entail_wit_1 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= (n_pre + 1 )) |] 
  &&  [| (0 = (fib_mod_z ((2 - 2 )) (mod_pre))) |] 
  &&  [| ((1 % ( mod_pre ) ) = (fib_mod_z ((2 - 1 )) (mod_pre))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (0 <= (1 % ( mod_pre ) )) |] 
  &&  [| ((1 % ( mod_pre ) ) < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  emp
.

Definition fibonacci_mod_entail_wit_2 := 
forall (mod_pre: Z) (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_mod_z ((i - 2 )) (mod_pre))) |] 
  &&  [| (b = (fib_mod_z ((i - 1 )) (mod_pre))) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a < mod_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "c" ) )) # Int  |-> ((a + b ) % ( mod_pre ) ))
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (b = (fib_mod_z (((i + 1 ) - 2 )) (mod_pre))) |] 
  &&  [| (((a + b ) % ( mod_pre ) ) = (fib_mod_z (((i + 1 ) - 1 )) (mod_pre))) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (0 <= ((a + b ) % ( mod_pre ) )) |] 
  &&  [| (((a + b ) % ( mod_pre ) ) < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  ((( &( "c" ) )) # Int  |->_)
.

Definition fibonacci_mod_return_wit_1 := 
forall (mod_pre: Z) (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  emp
|--
  [| (0 = (fib_mod_z (n_pre) (mod_pre))) |]
  &&  emp
.

Definition fibonacci_mod_return_wit_2 := 
forall (mod_pre: Z) (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (a = (fib_mod_z ((i - 2 )) (mod_pre))) |] 
  &&  [| (b = (fib_mod_z ((i - 1 )) (mod_pre))) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a < mod_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < mod_pre) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < mod_pre) |] 
  &&  [| (mod_pre <= 1073741824) |]
  &&  emp
|--
  [| (b = (fib_mod_z (n_pre) (mod_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_fibonacci_mod_safety_wit_1 : fibonacci_mod_safety_wit_1.
Axiom proof_of_fibonacci_mod_safety_wit_2 : fibonacci_mod_safety_wit_2.
Axiom proof_of_fibonacci_mod_safety_wit_3 : fibonacci_mod_safety_wit_3.
Axiom proof_of_fibonacci_mod_safety_wit_4 : fibonacci_mod_safety_wit_4.
Axiom proof_of_fibonacci_mod_safety_wit_5 : fibonacci_mod_safety_wit_5.
Axiom proof_of_fibonacci_mod_safety_wit_6 : fibonacci_mod_safety_wit_6.
Axiom proof_of_fibonacci_mod_safety_wit_7 : fibonacci_mod_safety_wit_7.
Axiom proof_of_fibonacci_mod_safety_wit_8 : fibonacci_mod_safety_wit_8.
Axiom proof_of_fibonacci_mod_safety_wit_9 : fibonacci_mod_safety_wit_9.
Axiom proof_of_fibonacci_mod_entail_wit_1 : fibonacci_mod_entail_wit_1.
Axiom proof_of_fibonacci_mod_entail_wit_2 : fibonacci_mod_entail_wit_2.
Axiom proof_of_fibonacci_mod_return_wit_1 : fibonacci_mod_return_wit_1.
Axiom proof_of_fibonacci_mod_return_wit_2 : fibonacci_mod_return_wit_2.

End VC_Correct.
