Require Import partition_nonnegative_goal partition_nonnegative_proof_auto partition_nonnegative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include partition_nonnegative_proof_auto.
  Include partition_nonnegative_proof_manual.
End VC_Correctness.
