From SimpleC.EE.CAV.verify_20260528_202044_sll_head Require Import sll_head_goal sll_head_proof_auto sll_head_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_strategy_proof.
  Include sll_head_proof_auto.
  Include sll_head_proof_manual.
End VC_Correctness.
