Require Import string_reverse_copy_goal string_reverse_copy_proof_auto string_reverse_copy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_reverse_copy_proof_auto.
  Include string_reverse_copy_proof_manual.
End VC_Correctness.
