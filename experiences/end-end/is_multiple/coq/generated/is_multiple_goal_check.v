From SimpleC.EE.CAV.verify_20260422_175633_is_multiple Require Import is_multiple_goal is_multiple_proof_auto is_multiple_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include is_multiple_proof_auto.
  Include is_multiple_proof_manual.
End VC_Correctness.
