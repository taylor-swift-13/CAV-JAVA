From SimpleC.EE.CAV.verify_20260422_152433_count_multiples Require Import count_multiples_goal count_multiples_proof_auto count_multiples_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include count_multiples_proof_auto.
  Include count_multiples_proof_manual.
End VC_Correctness.
