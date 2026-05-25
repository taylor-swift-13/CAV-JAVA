Require Import array_any_negative_goal array_any_negative_proof_auto array_any_negative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_any_negative_proof_auto.
  Include array_any_negative_proof_manual.
End VC_Correctness.
