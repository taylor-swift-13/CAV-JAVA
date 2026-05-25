From SimpleC.EE.CAV.verify_20260422_023444_array_clamp_nonnegative Require Import array_clamp_nonnegative_goal array_clamp_nonnegative_proof_auto array_clamp_nonnegative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_clamp_nonnegative_proof_auto.
  Include array_clamp_nonnegative_proof_manual.
End VC_Correctness.
