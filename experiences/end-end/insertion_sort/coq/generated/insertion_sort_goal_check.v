From SimpleC.EE.CAV.verify_20260422_174132_insertion_sort Require Import insertion_sort_goal insertion_sort_proof_auto insertion_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include insertion_sort_proof_auto.
  Include insertion_sort_proof_manual.
End VC_Correctness.
