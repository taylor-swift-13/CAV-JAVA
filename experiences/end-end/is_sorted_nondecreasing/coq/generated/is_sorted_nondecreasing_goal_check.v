From SimpleC.EE.CAV.verify_20260422_181654_is_sorted_nondecreasing Require Import is_sorted_nondecreasing_goal is_sorted_nondecreasing_proof_auto is_sorted_nondecreasing_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include is_sorted_nondecreasing_proof_auto.
  Include is_sorted_nondecreasing_proof_manual.
End VC_Correctness.
