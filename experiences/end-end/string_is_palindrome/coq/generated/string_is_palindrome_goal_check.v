From SimpleC.EE.CAV.verify_20260423_031617_string_is_palindrome Require Import string_is_palindrome_goal string_is_palindrome_proof_auto string_is_palindrome_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include string_is_palindrome_proof_auto.
  Include string_is_palindrome_proof_manual.
End VC_Correctness.
