From SimpleC.EE.CAV.verify_20260422_163304_fibonacci Require Import fibonacci_goal fibonacci_proof_auto fibonacci_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include fibonacci_proof_auto.
  Include fibonacci_proof_manual.
End VC_Correctness.
