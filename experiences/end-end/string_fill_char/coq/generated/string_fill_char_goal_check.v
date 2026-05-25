From SimpleC.EE.CAV.verify_20260423_023416_string_fill_char Require Import string_fill_char_goal string_fill_char_proof_auto string_fill_char_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_fill_char_proof_auto.
  Include string_fill_char_proof_manual.
End VC_Correctness.
