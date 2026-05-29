From SimpleC.EE.CAV.verify_20260527_absfastv_abs_value Require Import abs_value_goal abs_value_proof_auto abs_value_proof_manual.

Module VC_Correctness : VC_Correct.
  Include abs_value_proof_auto.
  Include abs_value_proof_manual.
End VC_Correctness.
