From SimpleC.EE.CAV.verify_20260422_234921_string_contains_char Require Import string_contains_char_goal string_contains_char_proof_auto string_contains_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_contains_char_proof_auto.
  Include string_contains_char_proof_manual.
End VC_Correctness.
