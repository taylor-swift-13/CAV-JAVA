From SimpleC.EE.CAV.verify_20260423_050130_sum_to_n Require Import sum_to_n_goal sum_to_n_proof_auto sum_to_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sum_to_n_proof_auto.
  Include sum_to_n_proof_manual.
End VC_Correctness.
