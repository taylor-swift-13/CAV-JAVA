From SimpleC.EE.CAV.verify_20260423_053250_upper_bound Require Import upper_bound_goal upper_bound_proof_auto upper_bound_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include upper_bound_proof_auto.
  Include upper_bound_proof_manual.
End VC_Correctness.
