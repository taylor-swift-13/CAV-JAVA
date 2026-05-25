From SimpleC.EE.CAV.verify_20260422_192331_max_subarray_sum Require Import max_subarray_sum_goal max_subarray_sum_proof_auto max_subarray_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include max_subarray_sum_proof_auto.
  Include max_subarray_sum_proof_manual.
End VC_Correctness.
