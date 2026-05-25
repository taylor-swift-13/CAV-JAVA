From SimpleC.EE.CAV.verify_20260423_054104_ways_to_reach Require Import ways_to_reach_goal ways_to_reach_proof_auto ways_to_reach_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include ways_to_reach_proof_auto.
  Include ways_to_reach_proof_manual.
End VC_Correctness.
