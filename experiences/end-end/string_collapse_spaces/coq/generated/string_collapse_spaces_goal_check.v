From SimpleC.EE.CAV.verify_20260422_224852_string_collapse_spaces Require Import string_collapse_spaces_goal string_collapse_spaces_proof_auto string_collapse_spaces_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_collapse_spaces_proof_auto.
  Include string_collapse_spaces_proof_manual.
End VC_Correctness.
