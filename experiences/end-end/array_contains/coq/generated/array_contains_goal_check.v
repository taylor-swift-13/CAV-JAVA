From SimpleC.EE.CAV.verify_20260422_024651_array_contains Require Import array_contains_goal array_contains_proof_auto array_contains_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_contains_proof_auto.
  Include array_contains_proof_manual.
End VC_Correctness.
