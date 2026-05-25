From SimpleC.EE.CAV.verify_20260422_133747_copy_array Require Import copy_array_goal copy_array_proof_auto copy_array_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include copy_array_proof_auto.
  Include copy_array_proof_manual.
End VC_Correctness.
