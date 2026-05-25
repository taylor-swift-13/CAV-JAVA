From SimpleC.EE.CAV.verify_20260423_030819_string_is_empty Require Import string_is_empty_goal string_is_empty_proof_auto string_is_empty_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_is_empty_proof_auto.
  Include string_is_empty_proof_manual.
End VC_Correctness.
