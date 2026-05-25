From SimpleC.EE.CAV.verify_20260422_212943_reverse_copy Require Import reverse_copy_goal reverse_copy_proof_auto reverse_copy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include reverse_copy_proof_auto.
  Include reverse_copy_proof_manual.
End VC_Correctness.
