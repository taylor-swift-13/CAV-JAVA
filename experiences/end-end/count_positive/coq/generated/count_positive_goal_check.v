From SimpleC.EE.CAV.verify_20260422_153249_count_positive Require Import count_positive_goal count_positive_proof_auto count_positive_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include count_positive_proof_auto.
  Include count_positive_proof_manual.
End VC_Correctness.
