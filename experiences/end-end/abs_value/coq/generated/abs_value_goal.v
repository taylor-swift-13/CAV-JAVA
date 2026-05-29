Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function abs_value -----*)

Definition abs_value_safety_wit_1 := 
forall (x_pre: Z) ,
  “ (x_pre >= (-INT_MAX)) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition abs_value_safety_wit_2 := 
forall (x_pre: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (x_pre >= (-INT_MAX)) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition abs_value_return_wit_1 := 
forall (x_pre: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (x_pre >= (-INT_MAX)) ”
  &&  emp
|--
  (“ (0 <= (-x_pre)) ” 
  &&  “ ((-x_pre) = x_pre) ”
  &&  emp)
  ||
  (“ (0 <= (-x_pre)) ” 
  &&  “ ((-x_pre) = (-x_pre)) ”
  &&  emp)
.

Definition abs_value_return_wit_2 := 
forall (x_pre: Z) ,
  “ (x_pre >= 0) ” 
  &&  “ (x_pre >= (-INT_MAX)) ”
  &&  emp
|--
  (“ (0 <= x_pre) ” 
  &&  “ (x_pre = x_pre) ”
  &&  emp)
  ||
  (“ (0 <= x_pre) ” 
  &&  “ (x_pre = (-x_pre)) ”
  &&  emp)
.

Module Type VC_Correct.


Axiom proof_of_abs_value_safety_wit_1 : abs_value_safety_wit_1.
Axiom proof_of_abs_value_safety_wit_2 : abs_value_safety_wit_2.
Axiom proof_of_abs_value_return_wit_1 : abs_value_return_wit_1.
Axiom proof_of_abs_value_return_wit_2 : abs_value_return_wit_2.

End VC_Correct.
