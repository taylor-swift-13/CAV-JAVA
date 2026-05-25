# Verification Issues

## Issue 1: workspace fingerprint initially had empty semantic fields

- Phenomenon: early in the task, `logs/workspace_fingerprint.json` still contained the script initialization placeholders:

```json
"semantic_description": "",
"keywords": {},
```

- Trigger: the workspace `output/verify_20260422_153249_count_positive` already existed before manual verify work began, but the workflow requires semantic retrieval metadata to be filled before annotation and proof work.
- Localization: `output/verify_20260422_153249_count_positive/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty description for a read-only array scan that counts positive values. The selected keywords use only the controlled vocabulary: `algorithm_family=counting`, `control_flow=for_loop`, `data_shape=array`, `semantic_intent=count_iterations`, `proof_pattern=[loop_invariant, case_split, range_bound]`, `numeric_properties=[nonnegative_input, int_range, monotone_accumulator]`, `edge_case_behavior=empty_loop_possible`, and after full verification `verification_status=goal_check_passed`.
- Result: the fingerprint no longer has empty semantic fields and can be used by later retrieval.

## Issue 2: the input C had no loop invariant or loop-exit assertion

- Phenomenon: the active annotated file initially matched the input and had a bare loop:

```c
int i;
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        cnt++;
    }
}

return cnt;
```

- Trigger: `count_positive` is a loop-based array scan. The verifier needs a loop-head invariant describing the processed prefix, the unchanged array resource, and unchanged parameters. Without it, the final result `cnt == count_positive_spec(l)` is not connected to the loop body updates.
- Localization: `annotated/verify_20260422_153249_count_positive.c`, immediately before and after the `for (i = 0; i < n; ++i)` loop.
- Fix action: added the prefix-count invariant and minimal exit assertion:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      cnt == count_positive_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }

/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      cnt == count_positive_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

- Why this fixes the issue: at the `for` guard, `i` is the next index to process and `cnt` equals the count over `sublist(0, i, l)`. The true branch `a[i] > 0` increments `cnt`, matching a one-element positive contribution; the false branch leaves `cnt` unchanged. On loop exit, `i >= n` and `i <= n` imply `i == n`, so the processed prefix is the whole list.
- Result: after clearing stale generated files and rerunning `symexec`, symbolic execution succeeded:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T15:40:47+08:00
symexec_elapsed=0
symexec_status=0
```

## Issue 3: generated manual proof contained five admitted witnesses

- Phenomenon: fresh symbolic execution generated `coq/generated/count_positive_proof_manual.v` with five admitted proof bodies:

```coq
Lemma proof_of_count_positive_safety_wit_4 : count_positive_safety_wit_4.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_1 : count_positive_entail_wit_1.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_2_1 : count_positive_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_2_2 : count_positive_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_count_positive_entail_wit_3 : count_positive_entail_wit_3.
Proof. Admitted.
```

- Trigger: the invariant introduced prefix-list obligations that the automatic proof did not discharge: the `cnt + 1` signed-int safety bound, empty-prefix initialization, positive and nonpositive branch extension of `count_positive_spec`, and loop-exit normalization from `sublist(0, i, l)` to `l`.
- Localization: `output/verify_20260422_153249_count_positive/coq/generated/count_positive_proof_manual.v`.
- Fix action: added two local helper lemmas and replaced all five admitted proof bodies:

```coq
Lemma count_positive_spec_app_single :
  forall (l : list Z) (x : Z),
    count_positive_spec (l ++ x :: nil) =
    count_positive_spec l + (if Z_gt_dec x 0 then 1 else 0).

Lemma count_positive_spec_bounds :
  forall (l : list Z),
    0 <= count_positive_spec l <= Zlength l.
```

- Why this fixes the issue: `count_positive_spec_app_single` rewrites `sublist 0 (i + 1) l` into the old prefix plus `Znth i l 0`, then each branch is discharged by splitting `Z_gt_dec (Znth i l 0) 0`. `count_positive_spec_bounds` proves `cnt <= i`; with `i < n_pre` and the existing int range for `n_pre`, it proves `cnt + 1` remains signed-int safe.
- Result: `coq/generated/count_positive_proof_manual.v` compiles and `rg -n "Admitted\\.|\\bAxiom\\b" .../count_positive_proof_manual.v` returns no matches.

## Issue 4: full Coq compilation and cleanup were required after proof repair

- Phenomenon: after proof repair, generated Coq build artifacts such as `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` existed under `coq/generated/`. The verify completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all to compile, followed by cleanup of non-`.v` Coq intermediates.
- Trigger: compiling the proof chain creates intermediate files even when every proof succeeds.
- Localization: `output/verify_20260422_153249_count_positive/coq/generated/` and `logs/compile.log`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled `original/count_positive.v`, `count_positive_goal.v`, `count_positive_proof_auto.v`, `count_positive_proof_manual.v`, and `count_positive_goal_check.v` with the documented load-path template. Then removed every non-`.v` file under workspace `coq/` and checked that there was no workspace `input/` directory containing extra generated files.
- Relevant compile result:

```text
compile_original_status=0
compile_goal_status=0
compile_proof_auto_status=0
compile_proof_manual_status=0
compile_goal_check_status=0
```

- Result: `goal_check.v` compiled successfully and `find coq -type f ! -name '*.v'` now returns no files.
