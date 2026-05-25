From SimpleC.EE.CAV.verify_20260422_014304_array_add Require Import array_add_goal array_add_proof_auto array_add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_add_proof_auto.
  Include array_add_proof_manual.
End VC_Correctness.
