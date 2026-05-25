Require Import bubble_sort_goal bubble_sort_proof_auto bubble_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include bubble_sort_proof_auto.
  Include bubble_sort_proof_manual.
End VC_Correctness.
