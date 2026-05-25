From SimpleC.EE.CAV.verify_20260423_052427_two_sum_sorted Require Import two_sum_sorted_goal two_sum_sorted_proof_auto two_sum_sorted_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include two_sum_sorted_proof_auto.
  Include two_sum_sorted_proof_manual.
End VC_Correctness.
