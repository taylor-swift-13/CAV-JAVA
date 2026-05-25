From SimpleC.EE.CAV.verify_20260423_021759_string_equal Require Import string_equal_goal string_equal_proof_auto string_equal_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_equal_proof_auto.
  Include string_equal_proof_manual.
End VC_Correctness.
