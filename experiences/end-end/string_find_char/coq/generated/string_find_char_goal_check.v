From SimpleC.EE.CAV.verify_20260423_024227_string_find_char Require Import string_find_char_goal string_find_char_proof_auto string_find_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_find_char_proof_auto.
  Include string_find_char_proof_manual.
End VC_Correctness.
