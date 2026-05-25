From SimpleC.EE.CAV.verify_20260422_180530_is_prime_simple Require Import is_prime_simple_goal is_prime_simple_proof_auto is_prime_simple_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include is_prime_simple_proof_auto.
  Include is_prime_simple_proof_manual.
End VC_Correctness.
