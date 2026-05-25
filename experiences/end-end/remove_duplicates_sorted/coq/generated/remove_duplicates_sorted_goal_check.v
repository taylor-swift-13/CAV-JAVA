From SimpleC.EE.CAV.verify_20260422_211833_remove_duplicates_sorted Require Import remove_duplicates_sorted_goal remove_duplicates_sorted_proof_auto remove_duplicates_sorted_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include remove_duplicates_sorted_proof_auto.
  Include remove_duplicates_sorted_proof_manual.
End VC_Correctness.
