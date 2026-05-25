From SimpleC.EE.CAV.verify_20260422_131939_climb_stairs Require Import climb_stairs_goal climb_stairs_proof_auto climb_stairs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include climb_stairs_proof_auto.
  Include climb_stairs_proof_manual.
End VC_Correctness.
