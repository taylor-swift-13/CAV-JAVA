From SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays Require Import merge_sorted_arrays_goal merge_sorted_arrays_proof_auto merge_sorted_arrays_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include merge_sorted_arrays_proof_auto.
  Include merge_sorted_arrays_proof_manual.
End VC_Correctness.
