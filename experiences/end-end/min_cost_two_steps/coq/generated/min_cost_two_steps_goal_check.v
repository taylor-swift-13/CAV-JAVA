From SimpleC.EE.CAV.verify_20260422_201546_min_cost_two_steps Require Import min_cost_two_steps_goal min_cost_two_steps_proof_auto min_cost_two_steps_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include min_cost_two_steps_proof_auto.
  Include min_cost_two_steps_proof_manual.
End VC_Correctness.
