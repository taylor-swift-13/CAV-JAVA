From SimpleC.EE.CAV.verify_20260422_045045_array_has_adjacent_equal Require Import array_has_adjacent_equal_goal array_has_adjacent_equal_proof_auto array_has_adjacent_equal_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_has_adjacent_equal_proof_auto.
  Include array_has_adjacent_equal_proof_manual.
End VC_Correctness.
