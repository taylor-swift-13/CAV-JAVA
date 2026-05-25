From SimpleC.EE.CAV.verify_20260422_190218_majority_candidate Require Import majority_candidate_goal majority_candidate_proof_auto majority_candidate_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include majority_candidate_proof_auto.
  Include majority_candidate_proof_manual.
End VC_Correctness.
