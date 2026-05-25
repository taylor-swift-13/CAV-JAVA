From SimpleC.EE.CAV.verify_20260422_164639_fibonacci_mod Require Import fibonacci_mod_goal fibonacci_mod_proof_auto fibonacci_mod_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include fibonacci_mod_proof_auto.
  Include fibonacci_mod_proof_manual.
End VC_Correctness.
