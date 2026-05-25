From SimpleC.EE.CAV.verify_20260422_154652_digit_sum Require Import digit_sum_goal digit_sum_proof_auto digit_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include digit_sum_proof_auto.
  Include digit_sum_proof_manual.
End VC_Correctness.
