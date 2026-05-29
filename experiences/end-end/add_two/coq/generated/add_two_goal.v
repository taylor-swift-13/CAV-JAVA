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

(*----- Function add_two -----*)

Definition add_two_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ ((INT_MIN) <= (a_pre + b_pre )) ” 
  &&  “ ((a_pre + b_pre ) <= INT_MAX) ”
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition add_two_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ ((INT_MIN) <= (a_pre + b_pre )) ” 
  &&  “ ((a_pre + b_pre ) <= INT_MAX) ”
  &&  emp
|--
  “ ((a_pre + b_pre ) = (a_pre + b_pre )) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_add_two_safety_wit_1 : add_two_safety_wit_1.
Axiom proof_of_add_two_return_wit_1 : add_two_return_wit_1.

End VC_Correct.
