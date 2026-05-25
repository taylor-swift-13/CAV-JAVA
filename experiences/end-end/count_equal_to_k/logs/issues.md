## Issue 1: workspace fingerprint was initialized with empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` initially had `"semantic_description": ""` and `"keywords": {}`.  The verify workflow requires these fields to be filled early, and `keywords` must use only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Trigger: this workspace was resumed from the existing directory `output/verify_20260422_151230_count_equal_to_k` before annotation and proof work.
- Localization: `logs/workspace_fingerprint.json`.
- Relevant original snippet:

```json
"semantic_description": "",
"keywords": {},
```

- Fix action: read `doc/retrieval/INDEX.md`, then filled a description for a read-only array counting scan and selected controlled terms only: `algorithm_family=counting`, `control_flow=for_loop`, `data_shape=array`, `semantic_intent=preserve_input`, `proof_pattern=[loop_invariant, case_split, range_bound, heap_reasoning]`, `numeric_properties=[nonnegative_input, int_range, monotone_accumulator]`, `edge_case_behavior=empty_loop_possible`.  After final verification, `verification_status` was updated to `goal_check_passed`.
- Result: the fingerprint now has non-empty semantic content and controlled-vocabulary keywords.

## Issue 2: the input C had no loop invariant or loop-exit assertion

- Phenomenon: the active annotated copy initially matched the input C and had a bare `for` loop:

```c
int i;
int ret = 0;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        ret++;
    }
}

return ret;
```

- Trigger: `count_equal_to_k` is a loop-based array scan.  The verifier needs a loop invariant at the `for` guard that records the processed prefix, preserved array ownership, and unchanged scalar parameters.
- Localization: `annotated/verify_20260422_151230_count_equal_to_k.c`, loop over `i`.
- Fix action: added a prefix-count invariant and a minimal loop-exit assertion:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      ret == count_equal_to_k_spec(sublist(0, i, l), k) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }

/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      ret == count_equal_to_k_spec(l, k@pre) &&
      IntArray::full(a, n, l)
*/
return ret;
```

- Why this fixes the issue: at loop entry, `ret` equals the count over `sublist(0, i, l)`.  The true branch `a[i] == k` advances the prefix count by one; the false branch advances the prefix with zero contribution.  On loop exit, `i >= n` plus `i <= n` gives `i == n`, so the prefix is the full list.
- Result: after clearing generated Coq files and rerunning `symexec`, symbolic execution succeeded:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T15:14:11+08:00
symexec_elapsed=0
symexec_status=0
```

## Issue 3: generated manual proof contained five admitted witnesses

- Phenomenon: fresh `symexec` generated `coq/generated/count_equal_to_k_proof_manual.v` with five `Admitted.` proof bodies:

```coq
Lemma proof_of_count_equal_to_k_safety_wit_3 : count_equal_to_k_safety_wit_3.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_1 : count_equal_to_k_entail_wit_1.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_2_1 : count_equal_to_k_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_2_2 : count_equal_to_k_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_count_equal_to_k_entail_wit_3 : count_equal_to_k_entail_wit_3.
Proof. Admitted.
```

- Trigger: the invariant introduces pure prefix-list obligations that the auto proof did not discharge: accumulator signed-int safety, initialization over the empty prefix, true/false branch prefix extension, and loop-exit prefix normalization.
- Localization: `coq/generated/count_equal_to_k_proof_manual.v`.
- Fix action: added two local helper lemmas and replaced all five admitted bodies:

```coq
Lemma count_equal_to_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    count_equal_to_k_spec (l ++ x :: nil) k =
    count_equal_to_k_spec l k + (if Z.eq_dec x k then 1 else 0).

Lemma count_equal_to_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= count_equal_to_k_spec l k <= Zlength l.
```

- Why this fixes the issue: `count_equal_to_k_spec_app_single` rewrites `sublist 0 (i + 1) l` into the old prefix plus `Znth i l 0`, allowing both branches to finish by splitting `Z.eq_dec (Znth i l 0) k_pre`.  `count_equal_to_k_spec_bounds` proves `ret <= i`, and with `i < n_pre` plus the stored signed-int range for `n_pre`, proves `ret + 1` is in range.  The exit witness asserts `i = n_pre`, rewrites with `Zlength l = n_pre`, and uses `sublist_self`.
- Result: `coq/generated/count_equal_to_k_proof_manual.v` compiled with status `0`, and `rg -n "Admitted\\.|\\bAxiom\\b" coq/generated/count_equal_to_k_proof_manual.v` returns no matches.

## Issue 4: successful symexec was not enough; the full Coq chain had to compile and intermediates had to be cleaned

- Phenomenon: after proof repair, generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files existed under `coq/generated/`.  The workflow requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, then requires non-`.v` intermediates under `coq/` to be removed.
- Trigger: compiling the full Coq chain creates build artifacts.
- Localization: `output/verify_20260422_151230_count_equal_to_k/coq/generated/`.
- Fix action: compiled, in order, `original/count_equal_to_k.v`, `count_equal_to_k_goal.v`, `count_equal_to_k_proof_auto.v`, `count_equal_to_k_proof_manual.v`, and `count_equal_to_k_goal_check.v` using the documented load-path template from `QualifiedCProgramming/SeparationLogic`.  Then deleted non-`.v` files under `coq/` and checked that workspace `input/` had no non-`.c`/non-`.v` files.
- Relevant compile result:

```text
compile_original_status=0
compile_goal_status=0
compile_proof_auto_status=0
compile_proof_manual_status=0
compile_goal_check_status=0
```

- Result: `goal_check.v` compiled successfully.  `find coq -type f ! -name '*.v'` now returns no files.
