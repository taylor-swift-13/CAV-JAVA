From SimpleC.EE.CAV.verify_20260423_033114_string_replace_char Require Import string_replace_char_goal string_replace_char_proof_auto string_replace_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_replace_char_proof_auto.
  Include string_replace_char_proof_manual.
End VC_Correctness.
