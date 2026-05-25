From SimpleC.EE.CAV.verify_20260422_055419_array_max Require Import array_max_goal array_max_proof_auto array_max_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_max_proof_auto.
  Include array_max_proof_manual.
End VC_Correctness.
