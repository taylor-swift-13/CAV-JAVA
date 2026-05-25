From SimpleC.EE.CAV.verify_20260422_093407_binary_search_last Require Import binary_search_last_goal binary_search_last_proof_auto binary_search_last_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include binary_search_last_proof_auto.
  Include binary_search_last_proof_manual.
End VC_Correctness.
