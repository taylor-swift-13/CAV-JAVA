From SimpleC.EE.CAV.verify_20260422_085356_array_sum_even_indices Require Import array_sum_even_indices_goal array_sum_even_indices_proof_auto array_sum_even_indices_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_sum_even_indices_proof_auto.
  Include array_sum_even_indices_proof_manual.
End VC_Correctness.
