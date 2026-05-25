From SimpleC.EE.CAV.verify_20260422_182720_lcm_simple Require Import lcm_simple_goal lcm_simple_proof_auto lcm_simple_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include lcm_simple_proof_auto.
  Include lcm_simple_proof_manual.
End VC_Correctness.
