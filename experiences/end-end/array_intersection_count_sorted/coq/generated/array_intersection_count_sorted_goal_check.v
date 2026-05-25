Require Import array_intersection_count_sorted_goal array_intersection_count_sorted_proof_auto array_intersection_count_sorted_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_intersection_count_sorted_proof_auto.
  Include array_intersection_count_sorted_proof_manual.
End VC_Correctness.
