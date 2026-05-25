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
Require Import power_nonnegative.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function power_nonnegative -----*)

Definition power_nonnegative_safety_wit_1 := 
forall (exp_pre: Z) (base_pre: Z) ,
  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition power_nonnegative_safety_wit_2 := 
forall (exp_pre: Z) (base_pre: Z) ,
  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition power_nonnegative_safety_wit_3 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) (i)) = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "ans" ) )) # Int  |-> (power_nonnegative_z (base_pre) (i)))
|--
  [| (((power_nonnegative_z (base_pre) (i)) * base_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((power_nonnegative_z (base_pre) (i)) * base_pre )) |]
.

Definition power_nonnegative_safety_wit_4 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) ((i + 1 ))) = (power_nonnegative_z (base_pre) ((i + 1 )))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_4))) /\ ((power_nonnegative_z (base_pre) (k_4)) <= INT_MAX))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "ans" ) )) # Int  |-> (power_nonnegative_z (base_pre) ((i + 1 ))))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition power_nonnegative_entail_wit_1 := 
forall (exp_pre: Z) (base_pre: Z) ,
  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  emp
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| (1 = (power_nonnegative_z (base_pre) (0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  emp
.

Definition power_nonnegative_entail_wit_2 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) (i)) = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |-> (power_nonnegative_z (base_pre) (i)))
.

Definition power_nonnegative_entail_wit_3 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) (i)) = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |-> ((power_nonnegative_z (base_pre) (i)) * base_pre ))
|--
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) ((i + 1 ))) = (power_nonnegative_z (base_pre) ((i + 1 )))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_4))) /\ ((power_nonnegative_z (base_pre) (k_4)) <= INT_MAX))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "ans" ) )) # Int  |-> (power_nonnegative_z (base_pre) ((i + 1 ))))
.

Definition power_nonnegative_entail_wit_4 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) ((i + 1 ))) = (power_nonnegative_z (base_pre) ((i + 1 )))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_4))) /\ ((power_nonnegative_z (base_pre) (k_4)) <= INT_MAX))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_3))) /\ ((power_nonnegative_z (base_pre) (k_3)) <= INT_MAX))) |] 
  &&  [| (i < exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  emp
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= exp_pre) |] 
  &&  [| ((power_nonnegative_z (base_pre) ((i + 1 ))) = (power_nonnegative_z (base_pre) ((i + 1 )))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  emp
.

Definition power_nonnegative_entail_wit_5 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| (i >= exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  [| ((power_nonnegative_z (base_pre) (exp_pre)) = (power_nonnegative_z (base_pre) (exp_pre))) |] 
  &&  [| (i >= exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  ((( &( "i" ) )) # Int  |-> exp_pre)
  **  ((( &( "ans" ) )) # Int  |-> (power_nonnegative_z (base_pre) (exp_pre)))
.

Definition power_nonnegative_return_wit_1 := 
forall (exp_pre: Z) (base_pre: Z) (ans: Z) (i: Z) ,
  [| ((power_nonnegative_z (base_pre) (exp_pre)) = (power_nonnegative_z (base_pre) (exp_pre))) |] 
  &&  [| (i >= exp_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= exp_pre) |] 
  &&  [| (ans = (power_nonnegative_z (base_pre) (i))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k_2))) /\ ((power_nonnegative_z (base_pre) (k_2)) <= INT_MAX))) |] 
  &&  [| (0 <= exp_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k <= exp_pre)) -> ((INT_MIN <= (power_nonnegative_z (base_pre) (k))) /\ ((power_nonnegative_z (base_pre) (k)) <= INT_MAX))) |]
  &&  emp
|--
  [| ((power_nonnegative_z (base_pre) (exp_pre)) = (power_nonnegative_z (base_pre) (exp_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_power_nonnegative_safety_wit_1 : power_nonnegative_safety_wit_1.
Axiom proof_of_power_nonnegative_safety_wit_2 : power_nonnegative_safety_wit_2.
Axiom proof_of_power_nonnegative_safety_wit_3 : power_nonnegative_safety_wit_3.
Axiom proof_of_power_nonnegative_safety_wit_4 : power_nonnegative_safety_wit_4.
Axiom proof_of_power_nonnegative_entail_wit_1 : power_nonnegative_entail_wit_1.
Axiom proof_of_power_nonnegative_entail_wit_2 : power_nonnegative_entail_wit_2.
Axiom proof_of_power_nonnegative_entail_wit_3 : power_nonnegative_entail_wit_3.
Axiom proof_of_power_nonnegative_entail_wit_4 : power_nonnegative_entail_wit_4.
Axiom proof_of_power_nonnegative_entail_wit_5 : power_nonnegative_entail_wit_5.
Axiom proof_of_power_nonnegative_return_wit_1 : power_nonnegative_return_wit_1.

End VC_Correct.
