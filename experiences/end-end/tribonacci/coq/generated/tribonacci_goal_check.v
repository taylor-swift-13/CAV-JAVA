From SimpleC.EE.CAV.verify_20260423_051744_tribonacci Require Import tribonacci_goal tribonacci_proof_auto tribonacci_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include tribonacci_proof_auto.
  Include tribonacci_proof_manual.
End VC_Correctness.
