From SimpleC.EE.CAV.verify_20260422_170350_gcd_iterative Require Import gcd_iterative_goal gcd_iterative_proof_auto gcd_iterative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include gcd_iterative_proof_auto.
  Include gcd_iterative_proof_manual.
End VC_Correctness.
