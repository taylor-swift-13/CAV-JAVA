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
Require Import count_multiples.
Require Import count_multiples_helper.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function count_multiples -----*)

Definition count_multiples_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_multiples_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_multiples_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((i <> (INT_MIN)) \/ (k_pre <> (-1))) |] 
  &&  [| (k_pre <> 0) |]
.

Definition count_multiples_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_multiples_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| ((i % ( k_pre ) ) = 0) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((cnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt + 1 )) |]
.

Definition count_multiples_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| ((i % ( k_pre ) ) <> 0) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_multiples_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| ((i % ( k_pre ) ) = 0) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_multiples_entail_wit_1 := 
forall (k_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (1 - 1 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (count_multiples_upto_z (k_pre) ((1 - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
.

Definition count_multiples_entail_wit_2_1 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| ((i % ( k_pre ) ) = 0) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (0 <= (cnt + 1 )) |] 
  &&  [| ((cnt + 1 ) <= ((i + 1 ) - 1 )) |] 
  &&  [| ((cnt + 1 ) <= n_pre) |] 
  &&  [| ((cnt + 1 ) = (count_multiples_upto_z (k_pre) (((i + 1 ) - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
.

Definition count_multiples_entail_wit_2_2 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| ((i % ( k_pre ) ) <> 0) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= ((i + 1 ) - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) (((i + 1 ) - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
.

Definition count_multiples_entail_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (cnt: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt <= (i - 1 )) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (cnt = (count_multiples_upto_z (k_pre) ((i - 1 )))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |]
  &&  emp
|--
  [| (i = (n_pre + 1 )) |] 
  &&  [| (cnt = (count_multiples_spec (n_pre) (k_pre))) |]
  &&  emp
.

Definition count_multiples_return_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (i: Z) (cnt: Z) ,
  [| (i = (n_pre + 1 )) |] 
  &&  [| (cnt = (count_multiples_spec (n_pre) (k_pre))) |]
  &&  emp
|--
  [| (cnt = (count_multiples_spec (n_pre) (k_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_count_multiples_safety_wit_1 : count_multiples_safety_wit_1.
Axiom proof_of_count_multiples_safety_wit_2 : count_multiples_safety_wit_2.
Axiom proof_of_count_multiples_safety_wit_3 : count_multiples_safety_wit_3.
Axiom proof_of_count_multiples_safety_wit_4 : count_multiples_safety_wit_4.
Axiom proof_of_count_multiples_safety_wit_5 : count_multiples_safety_wit_5.
Axiom proof_of_count_multiples_safety_wit_6 : count_multiples_safety_wit_6.
Axiom proof_of_count_multiples_safety_wit_7 : count_multiples_safety_wit_7.
Axiom proof_of_count_multiples_entail_wit_1 : count_multiples_entail_wit_1.
Axiom proof_of_count_multiples_entail_wit_2_1 : count_multiples_entail_wit_2_1.
Axiom proof_of_count_multiples_entail_wit_2_2 : count_multiples_entail_wit_2_2.
Axiom proof_of_count_multiples_entail_wit_3 : count_multiples_entail_wit_3.
Axiom proof_of_count_multiples_return_wit_1 : count_multiples_return_wit_1.

End VC_Correct.
