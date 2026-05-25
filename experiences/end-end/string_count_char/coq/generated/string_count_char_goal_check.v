From SimpleC.EE.CAV.verify_20260423_002212_string_count_char Require Import string_count_char_goal string_count_char_proof_auto string_count_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_count_char_proof_auto.
  Include string_count_char_proof_manual.
End VC_Correctness.
