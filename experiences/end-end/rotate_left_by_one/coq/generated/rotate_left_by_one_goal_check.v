From SimpleC.EE.CAV.verify_20260422_215602_rotate_left_by_one Require Import rotate_left_by_one_goal rotate_left_by_one_proof_auto rotate_left_by_one_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include rotate_left_by_one_proof_auto.
  Include rotate_left_by_one_proof_manual.
End VC_Correctness.
