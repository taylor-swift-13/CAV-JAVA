From SimpleC.EE.CAV.verify_20260423_044748_string_to_upper_ascii Require Import string_to_upper_ascii_goal string_to_upper_ascii_proof_auto string_to_upper_ascii_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_to_upper_ascii_proof_auto.
  Include string_to_upper_ascii_proof_manual.
End VC_Correctness.
