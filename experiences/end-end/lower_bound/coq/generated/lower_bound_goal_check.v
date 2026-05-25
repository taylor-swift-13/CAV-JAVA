From SimpleC.EE.CAV.verify_20260422_185520_lower_bound Require Import lower_bound_goal lower_bound_proof_auto lower_bound_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include lower_bound_proof_auto.
  Include lower_bound_proof_manual.
End VC_Correctness.
