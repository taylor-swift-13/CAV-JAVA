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
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Local Open Scope sac.
Require Import sll_strategy_goal.
Require Import sll_strategy_proof.

(*----- Function sll_head -----*)

Definition sll_head_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (x: Z) (y: Z) ,
  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l )
  **  ((&((p_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (x = x) ”
  &&  (sll p_pre (cons (x) (l)) )
.

Definition sll_head_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (x: Z) ,
  “ (p_pre <> 0) ”
  &&  (sll p_pre (cons (x) (l)) )
|--
  EX (y: Z) ,
  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l )
  **  ((&((p_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
.

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_sll_head_return_wit_1 : sll_head_return_wit_1.
Axiom proof_of_sll_head_partial_solve_wit_1 : sll_head_partial_solve_wit_1.

End VC_Correct.
