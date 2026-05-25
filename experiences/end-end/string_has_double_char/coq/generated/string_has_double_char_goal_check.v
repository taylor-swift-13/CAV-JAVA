From SimpleC.EE.CAV.verify_20260423_025651_string_has_double_char Require Import string_has_double_char_goal string_has_double_char_proof_auto string_has_double_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_has_double_char_proof_auto.
  Include string_has_double_char_proof_manual.
End VC_Correctness.
