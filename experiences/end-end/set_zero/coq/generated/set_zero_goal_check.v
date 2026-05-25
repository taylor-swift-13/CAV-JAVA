From SimpleC.EE.CAV.verify_20260422_222028_set_zero Require Import set_zero_goal set_zero_proof_auto set_zero_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include set_zero_proof_auto.
  Include set_zero_proof_manual.
End VC_Correctness.
