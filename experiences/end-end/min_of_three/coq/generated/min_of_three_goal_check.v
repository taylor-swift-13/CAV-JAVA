Require Import min_of_three_goal min_of_three_proof_auto min_of_three_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include min_of_three_proof_auto.
  Include min_of_three_proof_manual.
End VC_Correctness.
