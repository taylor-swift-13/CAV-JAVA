From SimpleC.EE.CAV.verify_20260422_071205_array_remove_value_to_output Require Import array_remove_value_to_output_goal array_remove_value_to_output_proof_auto array_remove_value_to_output_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_remove_value_to_output_proof_auto.
  Include array_remove_value_to_output_proof_manual.
End VC_Correctness.
