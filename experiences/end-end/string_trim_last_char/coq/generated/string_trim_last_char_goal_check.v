From SimpleC.EE.CAV.verify_20260423_045417_string_trim_last_char Require Import string_trim_last_char_goal string_trim_last_char_proof_auto string_trim_last_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_trim_last_char_proof_auto.
  Include string_trim_last_char_proof_manual.
End VC_Correctness.
