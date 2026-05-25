From SimpleC.EE.CAV.verify_20260423_003638_string_count_digits Require Import string_count_digits_goal string_count_digits_proof_auto string_count_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_count_digits_proof_auto.
  Include string_count_digits_proof_manual.
End VC_Correctness.
