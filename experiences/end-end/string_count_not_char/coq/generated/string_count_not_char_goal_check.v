From SimpleC.EE.CAV.verify_20260423_005835_string_count_not_char Require Import string_count_not_char_goal string_count_not_char_proof_auto string_count_not_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_count_not_char_proof_auto.
  Include string_count_not_char_proof_manual.
End VC_Correctness.
