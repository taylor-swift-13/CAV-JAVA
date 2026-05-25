## 2026-04-22 20:11 CST - Reuse archived proof after byte-identical regenerated goals

After restoring the archived loop invariant shape and rerunning `symexec`, the generated files in this workspace are non-empty:

```text
 98698 merge_sorted_arrays_goal.v
  3219 merge_sorted_arrays_proof_auto.v
  1859 merge_sorted_arrays_proof_manual.v
   498 merge_sorted_arrays_goal_check.v
```

The current manual proof file contains ten admitted witnesses:

```coq
proof_of_merge_sorted_arrays_entail_wit_1
proof_of_merge_sorted_arrays_entail_wit_2_1
proof_of_merge_sorted_arrays_entail_wit_2_2
proof_of_merge_sorted_arrays_entail_wit_3_1
proof_of_merge_sorted_arrays_entail_wit_3_2
proof_of_merge_sorted_arrays_entail_wit_4
proof_of_merge_sorted_arrays_entail_wit_5_1
proof_of_merge_sorted_arrays_entail_wit_5_2
proof_of_merge_sorted_arrays_entail_wit_6
proof_of_merge_sorted_arrays_return_wit_1
```

I compared the freshly generated `merge_sorted_arrays_goal.v` with the archived successful goal file at `./archieve/examples_backup_20260422_011624/merge_sorted_arrays/coq/generated/merge_sorted_arrays_goal.v`; `diff -u` produced no output, so the witness definitions and proof obligations are byte-identical. Therefore the archived manual proof is reusable under `PROOF.md` section 35: the VC body is identical and only the import logic path in `proof_manual.v` differs.

The proof needs the same helper lemmas recorded in `PROOF.md` section 21:

```coq
replace_Znth_app_suffix_head_Z
sublist_prefix_snoc_Z
merge_app_a_last
merge_app_b_last
Forall_sublist0_Znth_le_value
Forall_sublist0_Znth_lt_value
Zlength_merge_sorted_arrays_spec
```

These lemmas handle the pure list work left after `entailer!`: normalizing an output write at the end of the prefix, rewriting `sublist 0 (i+1)` into a snoc form, proving the merge-prefix semantic extension for either branch, and deriving `Forall` side conditions from invariant quantified facts. The witness proofs then only instantiate `Exists`, choose assertion-level `Left`/`Right` for phase disjunctions, and normalize the final full-prefix/empty-suffix return state.

Next edit: copy the archived helper lemmas and completed witness proofs into the current `coq/generated/merge_sorted_arrays_proof_manual.v`, keeping the current import line:

```coq
From SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays Require Import merge_sorted_arrays_goal.
```

Then compile `original/merge_sorted_arrays.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` with the standard load path.

## 2026-04-22 20:12 CST - Full proof and goal_check replay succeeded

After transplanting the archived proof and updating only the workspace import path, the current manual proof file starts with:

```coq
From SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays Require Import merge_sorted_arrays_goal.
Require Import merge_sorted_arrays.
Import ListNotations.
```

It contains the helper lemmas and concrete witness proofs from the archived byte-identical goal. A grep check found no remaining forbidden placeholders:

```text
rg -n 'Admitted\.|^\s*Axiom\b' output/verify_20260422_194235_merge_sorted_arrays/coq/generated/merge_sorted_arrays_proof_manual.v
```

produced no output.

The full compile replay from `QualifiedCProgramming/SeparationLogic` succeeded with the standard base `-R` flags, `-Q "$ORIG" ""`, and `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays"`:

```text
compiled original/merge_sorted_arrays.v
compiled merge_sorted_arrays_goal.v
compiled merge_sorted_arrays_proof_auto.v
compiled merge_sorted_arrays_proof_manual.v
compiled merge_sorted_arrays_goal_check.v
compile_status: 0
```

This closes the proof-stage blocker. The remaining required action is cleanup of non-`.v` compilation artifacts and final metrics update.
