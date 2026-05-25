From SimpleC.EE.CAV.verify_20260422_063057_array_pairwise_sum Require Import array_pairwise_sum_goal array_pairwise_sum_proof_auto array_pairwise_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_pairwise_sum_proof_auto.
  Include array_pairwise_sum_proof_manual.
End VC_Correctness.
