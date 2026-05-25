From SimpleC.EE.CAV.verify_20260423_043145_string_starts_with_char Require Import string_starts_with_char_goal string_starts_with_char_proof_auto string_starts_with_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_starts_with_char_proof_auto.
  Include string_starts_with_char_proof_manual.
End VC_Correctness.
