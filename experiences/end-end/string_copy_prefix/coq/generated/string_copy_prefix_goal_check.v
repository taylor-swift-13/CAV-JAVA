From SimpleC.EE.CAV.verify_20260423_000831_string_copy_prefix Require Import string_copy_prefix_goal string_copy_prefix_proof_auto string_copy_prefix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_copy_prefix_proof_auto.
  Include string_copy_prefix_proof_manual.
End VC_Correctness.
