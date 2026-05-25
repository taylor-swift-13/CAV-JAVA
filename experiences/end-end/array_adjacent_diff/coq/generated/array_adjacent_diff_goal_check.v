From SimpleC.EE.CAV.verify_20260422_015904_array_adjacent_diff Require Import array_adjacent_diff_goal array_adjacent_diff_proof_auto array_adjacent_diff_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_adjacent_diff_proof_auto.
  Include array_adjacent_diff_proof_manual.
End VC_Correctness.
