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
Require Import reverse_digits.
Require Import reverse_digits_verify_aux.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function reverse_digits -----*)

Definition reverse_digits_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_digits_safety_wit_2 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_digits_safety_wit_3 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (((ans * 10 ) + (n % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((ans * 10 ) + (n % ( 10 ) ) )) |]
.

Definition reverse_digits_safety_wit_4 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition reverse_digits_safety_wit_5 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| ((ans * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ans * 10 )) |]
.

Definition reverse_digits_safety_wit_6 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition reverse_digits_safety_wit_7 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition reverse_digits_safety_wit_8 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ((ans * 10 ) + (n % ( 10 ) ) ))
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition reverse_digits_safety_wit_9 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ans" ) )) # Int  |-> ((ans * 10 ) + (n % ( 10 ) ) ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition reverse_digits_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ans" ) )) # Int  |-> 0)
.

Definition reverse_digits_entail_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n_pre) (0)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  emp
.

Definition reverse_digits_entail_wit_3 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= (n ÷ 10 )) |] 
  &&  [| ((n ÷ 10 ) <= INT_MAX) |] 
  &&  [| (0 <= ((ans * 10 ) + (n % ( 10 ) ) )) |] 
  &&  [| (((ans * 10 ) + (n % ( 10 ) ) ) <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z ((n ÷ 10 )) (((ans * 10 ) + (n % ( 10 ) ) ))) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  emp
.

Definition reverse_digits_entail_wit_4 := 
forall (n_pre: Z) (ans: Z) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= ans) |] 
  &&  [| (ans <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |] 
  &&  [| ((reverse_digits_acc_z (n) (ans)) = (reverse_digits_z (n_pre))) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= INT_MAX) |] 
  &&  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= (reverse_digits_z (n_pre))) |] 
  &&  [| ((reverse_digits_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (n = 0) |] 
  &&  [| (ans = (reverse_digits_z (n_pre))) |]
  &&  emp
.

Definition reverse_digits_return_wit_1 := 
forall (n_pre: Z) (n: Z) (ans: Z) ,
  [| (n = 0) |] 
  &&  [| (ans = (reverse_digits_z (n_pre))) |]
  &&  emp
|--
  [| (ans = (reverse_digits_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_reverse_digits_safety_wit_1 : reverse_digits_safety_wit_1.
Axiom proof_of_reverse_digits_safety_wit_2 : reverse_digits_safety_wit_2.
Axiom proof_of_reverse_digits_safety_wit_3 : reverse_digits_safety_wit_3.
Axiom proof_of_reverse_digits_safety_wit_4 : reverse_digits_safety_wit_4.
Axiom proof_of_reverse_digits_safety_wit_5 : reverse_digits_safety_wit_5.
Axiom proof_of_reverse_digits_safety_wit_6 : reverse_digits_safety_wit_6.
Axiom proof_of_reverse_digits_safety_wit_7 : reverse_digits_safety_wit_7.
Axiom proof_of_reverse_digits_safety_wit_8 : reverse_digits_safety_wit_8.
Axiom proof_of_reverse_digits_safety_wit_9 : reverse_digits_safety_wit_9.
Axiom proof_of_reverse_digits_entail_wit_1 : reverse_digits_entail_wit_1.
Axiom proof_of_reverse_digits_entail_wit_2 : reverse_digits_entail_wit_2.
Axiom proof_of_reverse_digits_entail_wit_3 : reverse_digits_entail_wit_3.
Axiom proof_of_reverse_digits_entail_wit_4 : reverse_digits_entail_wit_4.
Axiom proof_of_reverse_digits_return_wit_1 : reverse_digits_return_wit_1.

End VC_Correct.
