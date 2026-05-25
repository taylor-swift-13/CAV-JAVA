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
Require Import count_divisors.
Require Import count_divisors_helper.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function count_divisors -----*)

Definition count_divisors_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_divisors_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_divisors_safety_wit_3 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((n_pre <> (INT_MIN)) \/ (d <> (-1))) |] 
  &&  [| (d <> 0) |]
.

Definition count_divisors_safety_wit_4 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_divisors_safety_wit_5 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((cnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt + 1 )) |]
.

Definition count_divisors_safety_wit_6 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((d + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d + 1 )) |]
.

Definition count_divisors_safety_wit_7 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  [| ((d + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d + 1 )) |]
.

Definition count_divisors_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (1 - 1 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (count_divisors_upto_z (n_pre) ((1 - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition count_divisors_entail_wit_2_1 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= (d + 1 )) |] 
  &&  [| ((d + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (0 <= (cnt + 1 )) |] 
  &&  [| ((cnt + 1 ) <= ((d + 1 ) - 1 )) |] 
  &&  [| ((cnt + 1 ) <= n_pre) |] 
  &&  [| ((cnt + 1 ) = (count_divisors_upto_z (n_pre) (((d + 1 ) - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition count_divisors_entail_wit_2_2 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= (d + 1 )) |] 
  &&  [| ((d + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= ((d + 1 ) - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) (((d + 1 ) - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition count_divisors_entail_wit_3 := 
forall (n_pre: Z) (cnt: Z) (d: Z) ,
  [| (d > n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= d) |] 
  &&  [| (d <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (d - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_divisors_upto_z (n_pre) ((d - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (d = (n_pre + 1 )) |] 
  &&  [| (cnt = (count_divisors_spec (n_pre))) |]
  &&  emp
.

Definition count_divisors_return_wit_1 := 
forall (n_pre: Z) (d: Z) (cnt: Z) ,
  [| (d = (n_pre + 1 )) |] 
  &&  [| (cnt = (count_divisors_spec (n_pre))) |]
  &&  emp
|--
  [| (cnt = (count_divisors_spec (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_count_divisors_safety_wit_1 : count_divisors_safety_wit_1.
Axiom proof_of_count_divisors_safety_wit_2 : count_divisors_safety_wit_2.
Axiom proof_of_count_divisors_safety_wit_3 : count_divisors_safety_wit_3.
Axiom proof_of_count_divisors_safety_wit_4 : count_divisors_safety_wit_4.
Axiom proof_of_count_divisors_safety_wit_5 : count_divisors_safety_wit_5.
Axiom proof_of_count_divisors_safety_wit_6 : count_divisors_safety_wit_6.
Axiom proof_of_count_divisors_safety_wit_7 : count_divisors_safety_wit_7.
Axiom proof_of_count_divisors_entail_wit_1 : count_divisors_entail_wit_1.
Axiom proof_of_count_divisors_entail_wit_2_1 : count_divisors_entail_wit_2_1.
Axiom proof_of_count_divisors_entail_wit_2_2 : count_divisors_entail_wit_2_2.
Axiom proof_of_count_divisors_entail_wit_3 : count_divisors_entail_wit_3.
Axiom proof_of_count_divisors_return_wit_1 : count_divisors_return_wit_1.

End VC_Correct.
