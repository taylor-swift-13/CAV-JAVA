From SimpleC.EE.CAV.verify_20260423_041814_string_set_a Require Import string_set_a_goal string_set_a_proof_auto string_set_a_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_set_a_proof_auto.
  Include string_set_a_proof_manual.
End VC_Correctness.
