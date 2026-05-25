From SimpleC.EE.CAV.verify_20260422_054629_array_longest_nonnegative_run Require Import array_longest_nonnegative_run_goal array_longest_nonnegative_run_proof_auto array_longest_nonnegative_run_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_longest_nonnegative_run_proof_auto.
  Include array_longest_nonnegative_run_proof_manual.
End VC_Correctness.
