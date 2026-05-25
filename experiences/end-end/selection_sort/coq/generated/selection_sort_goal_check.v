From SimpleC.EE.CAV.verify_20260422_220436_selection_sort Require Import selection_sort_goal selection_sort_proof_auto selection_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include selection_sort_proof_auto.
  Include selection_sort_proof_manual.
End VC_Correctness.
