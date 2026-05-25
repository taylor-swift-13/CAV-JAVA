From SimpleC.EE.CAV.verify_20260422_090412_array_swap_ends Require Import array_swap_ends_goal array_swap_ends_proof_auto array_swap_ends_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_swap_ends_proof_auto.
  Include array_swap_ends_proof_manual.
End VC_Correctness.
