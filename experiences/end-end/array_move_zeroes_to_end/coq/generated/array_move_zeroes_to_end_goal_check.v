From SimpleC.EE.CAV.verify_20260422_061035_array_move_zeroes_to_end Require Import array_move_zeroes_to_end_goal array_move_zeroes_to_end_proof_auto array_move_zeroes_to_end_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_move_zeroes_to_end_proof_auto.
  Include array_move_zeroes_to_end_proof_manual.
End VC_Correctness.
