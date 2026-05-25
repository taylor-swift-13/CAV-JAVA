From SimpleC.EE.CAV.verify_20260422_032621_array_count_increasing_steps Require Import array_count_increasing_steps_goal array_count_increasing_steps_proof_auto array_count_increasing_steps_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_count_increasing_steps_proof_auto.
  Include array_count_increasing_steps_proof_manual.
End VC_Correctness.
