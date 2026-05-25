From SimpleC.EE.CAV.verify_20260422_080741_array_scale Require Import array_scale_goal array_scale_proof_auto array_scale_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_scale_proof_auto.
  Include array_scale_proof_manual.
End VC_Correctness.
