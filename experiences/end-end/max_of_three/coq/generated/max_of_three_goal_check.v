From SimpleC.EE.CAV.verify_20260422_191241_max_of_three Require Import max_of_three_goal max_of_three_proof_auto max_of_three_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include max_of_three_proof_auto.
  Include max_of_three_proof_manual.
End VC_Correctness.
