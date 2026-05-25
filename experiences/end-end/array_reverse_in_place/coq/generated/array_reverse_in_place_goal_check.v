From SimpleC.EE.CAV.verify_20260422_074343_array_reverse_in_place Require Import array_reverse_in_place_goal array_reverse_in_place_proof_auto array_reverse_in_place_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_reverse_in_place_proof_auto.
  Include array_reverse_in_place_proof_manual.
End VC_Correctness.
