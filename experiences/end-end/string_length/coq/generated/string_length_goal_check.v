From SimpleC.EE.CAV.verify_20260423_121011_string_length Require Import string_length_goal string_length_proof_auto string_length_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_length_proof_auto.
  Include string_length_proof_manual.
End VC_Correctness.
