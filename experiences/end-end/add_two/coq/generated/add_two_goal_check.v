From SimpleC.EE.CAV.verify_20260527_193100v1_add_two Require Import add_two_goal add_two_proof_auto add_two_proof_manual.

Module VC_Correctness : VC_Correct.
  Include add_two_proof_auto.
  Include add_two_proof_manual.
End VC_Correctness.
