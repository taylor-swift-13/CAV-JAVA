From SimpleC.EE.CAV.verify_20260422_210632_prefix_sum Require Import prefix_sum_goal prefix_sum_proof_auto prefix_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include prefix_sum_proof_auto.
  Include prefix_sum_proof_manual.
End VC_Correctness.
