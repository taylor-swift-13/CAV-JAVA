From SimpleC.EE.CAV.verify_20260423_012416_string_count_vowels Require Import string_count_vowels_goal string_count_vowels_proof_auto string_count_vowels_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_count_vowels_proof_auto.
  Include string_count_vowels_proof_manual.
End VC_Correctness.
