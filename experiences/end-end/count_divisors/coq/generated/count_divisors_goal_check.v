From SimpleC.EE.CAV.verify_20260422_145616_count_divisors Require Import count_divisors_goal count_divisors_proof_auto count_divisors_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include count_divisors_proof_auto.
  Include count_divisors_proof_manual.
End VC_Correctness.
