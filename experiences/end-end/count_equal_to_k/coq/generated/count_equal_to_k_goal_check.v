From SimpleC.EE.CAV.verify_20260422_151230_count_equal_to_k Require Import count_equal_to_k_goal count_equal_to_k_proof_auto count_equal_to_k_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include count_equal_to_k_proof_auto.
  Include count_equal_to_k_proof_manual.
End VC_Correctness.
