From SimpleC.EE.CAV.verify_20260422_161944_factorial Require Import factorial_goal factorial_proof_auto factorial_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include factorial_proof_auto.
  Include factorial_proof_manual.
End VC_Correctness.
