From SimpleC.EE.CAV.verify_20260422_223908_string_all_lowercase Require Import string_all_lowercase_goal string_all_lowercase_proof_auto string_all_lowercase_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_all_lowercase_proof_auto.
  Include string_all_lowercase_proof_manual.
End VC_Correctness.
