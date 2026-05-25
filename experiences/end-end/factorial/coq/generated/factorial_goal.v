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

(*----- Function fac -----*)

Definition fac_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fac_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fac_safety_wit_3 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial ((i - 1 ))) = (factorial ((i - 1 )))) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "res" ) )) # Int  |-> (factorial ((i - 1 ))))
|--
  [| (((factorial ((i - 1 ))) * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((factorial ((i - 1 ))) * i )) |]
.

Definition fac_safety_wit_4 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial (i)) = (factorial (i))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "res" ) )) # Int  |-> (factorial (i)))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fac_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  emp
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| (1 = (factorial ((1 - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  emp
.

Definition fac_entail_wit_2 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |-> res)
|--
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial ((i - 1 ))) = (factorial ((i - 1 )))) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |-> (factorial ((i - 1 ))))
.

Definition fac_entail_wit_3 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial ((i - 1 ))) = (factorial ((i - 1 )))) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |-> ((factorial ((i - 1 ))) * i ))
|--
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial (i)) = (factorial (i))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "res" ) )) # Int  |-> (factorial (i)))
.

Definition fac_entail_wit_4 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((factorial (i)) = (factorial (i))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  emp
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| ((factorial (i)) = (factorial (((i + 1 ) - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  emp
.

Definition fac_entail_wit_5 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| ((factorial (n_pre)) = (factorial (n_pre))) |] 
  &&  [| (i > n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  ((( &( "i" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "res" ) )) # Int  |-> (factorial (n_pre)))
.

Definition fac_return_wit_1 := 
forall (n_pre: Z) (res: Z) (i: Z) ,
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| ((factorial (n_pre)) = (factorial (n_pre))) |] 
  &&  [| (i > n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (res = (factorial ((i - 1 )))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 10) |]
  &&  emp
|--
  [| ((factorial (n_pre)) = (factorial (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_fac_safety_wit_1 : fac_safety_wit_1.
Axiom proof_of_fac_safety_wit_2 : fac_safety_wit_2.
Axiom proof_of_fac_safety_wit_3 : fac_safety_wit_3.
Axiom proof_of_fac_safety_wit_4 : fac_safety_wit_4.
Axiom proof_of_fac_entail_wit_1 : fac_entail_wit_1.
Axiom proof_of_fac_entail_wit_2 : fac_entail_wit_2.
Axiom proof_of_fac_entail_wit_3 : fac_entail_wit_3.
Axiom proof_of_fac_entail_wit_4 : fac_entail_wit_4.
Axiom proof_of_fac_entail_wit_5 : fac_entail_wit_5.
Axiom proof_of_fac_return_wit_1 : fac_return_wit_1.

End VC_Correct.
