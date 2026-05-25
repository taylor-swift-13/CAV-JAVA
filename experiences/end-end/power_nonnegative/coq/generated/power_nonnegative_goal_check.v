From SimpleC.EE.CAV.verify_20260422_205655_power_nonnegative Require Import power_nonnegative_goal power_nonnegative_proof_auto power_nonnegative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include power_nonnegative_proof_auto.
  Include power_nonnegative_proof_manual.
End VC_Correctness.
