## 2026-04-22 20:47:00 +0800 - Fingerprint initially had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` was still at the bootstrap state with `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires filling these fields early so later agents can retrieve similar examples without opening source files first.
- Location: `output/verify_20260422_204612_partition_nonnegative/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md` and filled a non-empty semantic description. The keyword keys and values were chosen only from the controlled vocabulary: `algorithm_family=two_pointers`, `control_flow=[while_loop, if]`, `data_shape=[array, pointer]`, `semantic_intent=in_place_update`, `proof_pattern=[loop_invariant, case_split, range_bound, heap_reasoning]`, `numeric_properties=[nonnegative_input, int_range]`, and `edge_case_behavior=empty_loop_possible`. After final verification, added `verification_status=[goal_check_passed, proof_check_passed, auto_proof_contains_admitted, generated_goal_contains_axioms]`.
- Result: the fingerprint is independently useful for retrieval and records the final verification status.

## 2026-04-22 20:47:00 +0800 - Active annotated C had no loop invariant

- Phenomenon: the active annotated file initially copied the input C exactly and the only `while (i <= j)` loop had no `Inv`.
- Trigger: the postcondition depends on facts that must survive multiple iterations: `[0, i)` contains only negative elements, `(j, n)` contains only nonnegative elements, the array list keeps length `n@pre`, the array is still a permutation of the input list, and `a`/`n` are unchanged.
- Location: `annotated/verify_20260422_204612_partition_nonnegative.c`, immediately before the `while (i <= j)` loop.
- Fix action: added an existential current-list invariant:

```c
/*@ Inv exists lc,
      0 <= i && i <= j + 1 &&
      -1 <= j && j < n@pre &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lc[k] < 0) &&
      (forall (k: Z), (j < k && k < n@pre) => lc[k] >= 0) &&
      Permutation(l, lc) &&
      IntArray::full(a, n@pre, lc)
*/
while (i <= j) {
```

- Why this fixes the annotation gap: initialization uses `lc = l`; the negative branch extends the prefix; the swap branch places a known nonnegative value at old `j` and decrements `j`; loop exit has `i > j` and `i <= j + 1`, hence `i == j + 1`, so the prefix and suffix facts directly imply the two universal postconditions.
- Result: rerunning `QualifiedCProgramming/linux-binary/symexec` against the updated active annotated file succeeded and generated fresh `partition_nonnegative_goal.v`, `partition_nonnegative_proof_auto.v`, `partition_nonnegative_proof_manual.v`, and `partition_nonnegative_goal_check.v`.

Relevant `logs/qcp_run.log` ending:

```text
End of symbolic execution of function partition_nonnegative
Start to print Coq files for the program annotated/verify_20260422_204612_partition_nonnegative.c
Successfully finished symbolic execution
symexec_end=2026-04-22T20:48:05+08:00
symexec_elapsed=2
symexec_status=0
```

## 2026-04-22 20:48:20 +0800 - Two manual entail witnesses were generated

- Phenomenon: fresh `coq/generated/partition_nonnegative_proof_manual.v` contained two admitted manual obligations:

```coq
Lemma proof_of_partition_nonnegative_entail_wit_1 : partition_nonnegative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_partition_nonnegative_entail_wit_2_1 : partition_nonnegative_entail_wit_2_1.
Proof. Admitted.
```

- Trigger: `entail_wit_1` initializes the invariant, and `entail_wit_2_1` preserves it through the swap branch where the current list becomes `replace_Znth j (Znth i lc_2 0) (replace_Znth i (Znth j lc_2 0) lc_2)`.
- Location: `output/verify_20260422_204612_partition_nonnegative/coq/generated/partition_nonnegative_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_nth`/`replace_Znth` length, `Znth` after replacement, and a `partition_nonnegative_swap_perm` lemma proving that the two-position replacement is a permutation. The first witness chooses `Exists l`; the second chooses `Exists (partition_nonnegative_swap lc_2 i j)`.
- Result: `partition_nonnegative_proof_manual.v` now compiles and contains no `Admitted.` or top-level `Axiom`.

## 2026-04-22 20:51:00 +0800 - Archived proof needed current witness-name and bullet-order adjustments

- Phenomenon: the first proof compile after copying the archived same-task proof failed with:

```text
line 347: Error: The variable l_cur_2 was not found in the current environment.
```

Then, after renaming that variable, it failed with:

```text
line 354: Error: No product even after head-reduction.
```

- Trigger: the archived proof used the generated variable name `l_cur_2`, while the current witness uses `lc_2`. Its post-`entailer!` subgoal order also differed from the current generated VC.
- Location: `coq/generated/partition_nonnegative_proof_manual.v`, theorem `proof_of_partition_nonnegative_entail_wit_2_1`.
- Fix action: replaced `l_cur_2` with `lc_2`, inspected the live Coq state after:

```coq
pre_process.
Exists (partition_nonnegative_swap lc_2 i j).
Intros.
prop_apply IntArray.full_length.
entailer!; try lia.
```

The remaining subgoal order was heap, permutation, suffix, prefix, length. Reordered the proof bullets accordingly:

```coq
- unfold partition_nonnegative_swap.
  sep_apply store_int_undef_store_int.
  entailer!.
- eapply Permutation_trans.
  + exact H9.
  + apply partition_nonnegative_swap_perm.
    rewrite H6. lia.
- intros q Hq. ...
- intros p Hp. ...
- rewrite partition_nonnegative_swap_length.
  exact H6.
```

- Result: after this adjustment, full Coq compilation reached and passed `partition_nonnegative_goal_check.v`.

## 2026-04-22 20:52:54 +0800 - Full compile replay and cleanup

- Phenomenon: successful `symexec` and manual proof are not enough; the workflow requires compiling `goal`, `proof_auto`, `proof_manual`, and `goal_check`, then removing non-`.v` Coq intermediates.
- Trigger: `coqc` creates `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Location: `output/verify_20260422_204612_partition_nonnegative/coq/generated/` and `logs/compile_full.log`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` using the base `_CoqProject` load paths, `-Q "$ORIG" ""`, and `-Q "$GEN" ""`. The generated files use unqualified `Require Import partition_nonnegative_goal`, so the generated directory was placed on the empty logical path. There is no `original/partition_nonnegative.v`, so that optional step was skipped.
- Result: `partition_nonnegative_goal.v`, `partition_nonnegative_proof_auto.v`, `partition_nonnegative_proof_manual.v`, and `partition_nonnegative_goal_check.v` all compiled successfully. After cleanup, `find .../coq -type f ! -name '*.v'` returned no files. There were no non-`.c`/`.v` files under `input/`.

Relevant compile log:

```text
compile_start=2026-04-22T20:52:51+08:00
skip original/partition_nonnegative.v: not present
compile partition_nonnegative_goal.v
compile partition_nonnegative_proof_auto.v
compile partition_nonnegative_proof_manual.v
compile partition_nonnegative_goal_check.v
compile_end=2026-04-22T20:52:54+08:00
```
