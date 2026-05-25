From SimpleC.EE.CAV.verify_20260422_072722_array_replace_k Require Import array_replace_k_goal array_replace_k_proof_auto array_replace_k_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_replace_k_proof_auto.
  Include array_replace_k_proof_manual.
End VC_Correctness.
