From SimpleC.EE.CAV.verify_20260422_184334_longest_increasing_run Require Import longest_increasing_run_goal longest_increasing_run_proof_auto longest_increasing_run_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include longest_increasing_run_proof_auto.
  Include longest_increasing_run_proof_manual.
End VC_Correctness.
