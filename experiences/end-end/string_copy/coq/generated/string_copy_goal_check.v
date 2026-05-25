From SimpleC.EE.CAV.verify_20260422_235720_string_copy Require Import string_copy_goal string_copy_proof_auto string_copy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_copy_proof_auto.
  Include string_copy_proof_manual.
End VC_Correctness.
