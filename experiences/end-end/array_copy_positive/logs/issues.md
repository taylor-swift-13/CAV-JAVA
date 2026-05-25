## Issue 1: fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was still at the bootstrap state with an empty `semantic_description` and `{}` for `keywords`.
- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and then filling the fingerprint using only the controlled vocabulary in that file.
- Localization: `output/verify_20260422_025204_array_copy_positive/logs/workspace_fingerprint.json`.
- Fix action: filled the semantic description with the behavior of `array_copy_positive`: a single `for` loop scans `a[0..n)`, preserves `a`, mutates `out[0..n)`, writes `la[i]` for positive input values, writes `0` for nonpositive input values, and may execute zero iterations when `n == 0`. The controlled keywords now include `algorithm_family: selection`, `control_flow: [for_loop, if]`, `data_shape: [array, pointer]`, `semantic_intent: [preserve_input, in_place_update]`, `proof_pattern: [loop_invariant, case_split, heap_reasoning, range_bound]`, `numeric_properties: [nonnegative_input, int_range]`, and final `verification_status: [goal_check_passed, proof_check_passed]`.
- Result: the fingerprint is non-empty and uses only keys and values from `doc/retrieval/INDEX.md`.

## Issue 2: loop initially had no invariant for progressively written output

- Phenomenon: the active annotated file initially copied `input/array_copy_positive.c` exactly. The loop

```c
for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        out[i] = a[i];
    } else {
        out[i] = 0;
    }
}
```

had no `Inv`, so symbolic execution had no loop-head state describing the current logical contents of `out` or the processed prefix relation.

- Trigger: this function writes one output cell per iteration. Without an invariant, the verifier cannot preserve the input array, track the already transformed output prefix, keep the untouched suffix, or derive the postcondition at loop exit.
- Localization: `annotated/verify_20260422_025204_array_copy_positive.c`.
- Fix action: added an invariant with `exists lr`, bounds `0 <= i && i <= n@pre`, parameter equalities `n == n@pre`, `a == a@pre`, `out == out@pre`, length facts for `la`, `lo`, and `lr`, two split prefix implications, a suffix relation to `lo`, and heap ownership:

```c
(forall (k: Z), (0 <= k && k < i && la[k] > 0) => lr[k] == la[k]) &&
(forall (k: Z), (0 <= k && k < i && la[k] <= 0) => lr[k] == 0) &&
(forall (k: Z), (i <= k && k < n@pre) => lr[k] == lo[k]) &&
IntArray::full(a, n@pre, la) *
IntArray::full(out, n@pre, lr)
```

Added a minimal loop-exit `Assert` immediately after the loop that fixes `i == n` and exposes the postcondition-shaped prefix facts over `0 <= k < n@pre`.
- Result: `symexec` succeeded with the updated annotated file and generated fresh `array_copy_positive_goal.v`, `array_copy_positive_proof_auto.v`, `array_copy_positive_proof_manual.v`, and `array_copy_positive_goal_check.v`.

## Issue 3: `symexec` had to be run with explicit input and fresh generated files

- Phenomenon: the workspace initially had no generated Coq files. After editing `Inv` and `Assert`, the workflow required deleting stale generated targets and rerunning symbolic execution from the active annotated C.
- Trigger: generated Coq files must match the latest annotation; older files would mix stale witness shapes with the new invariant.
- Localization: `logs/qcp_run.log` and `coq/generated/`.
- Fix action: created `coq/generated`, deleted any existing generated targets for this function, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_025204_array_copy_positive.c \
  --goal-file=output/verify_20260422_025204_array_copy_positive/coq/generated/array_copy_positive_goal.v \
  --proof-auto-file=output/verify_20260422_025204_array_copy_positive/coq/generated/array_copy_positive_proof_auto.v \
  --proof-manual-file=output/verify_20260422_025204_array_copy_positive/coq/generated/array_copy_positive_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_025204_array_copy_positive \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T02:54:03+08:00
symexec_elapsed=0
symexec_status=0
```

## Issue 4: manual proof file contained three admitted entailment witnesses

- Phenomenon: after `symexec`, `coq/generated/array_copy_positive_proof_manual.v` contained:

```coq
Lemma proof_of_array_copy_positive_entail_wit_2_1 : array_copy_positive_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_copy_positive_entail_wit_2_2 : array_copy_positive_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_copy_positive_entail_wit_3 : array_copy_positive_entail_wit_3.
Proof. Admitted.
```

- Trigger: the two branch witnesses had to show that `replace_Znth` advances the logical output list from prefix length `i` to `i + 1`; the exit witness had to expose `i = n_pre`.
- Localization: `coq/generated/array_copy_positive_proof_manual.v`, lemmas `proof_of_array_copy_positive_entail_wit_2_1`, `proof_of_array_copy_positive_entail_wit_2_2`, and `proof_of_array_copy_positive_entail_wit_3`.
- Fix action: added local helper lemmas for `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`. For the positive branch, chose `replace_Znth i (Znth i la 0) lr_2` as the witness list; for the nonpositive branch, chose `replace_Znth i 0 lr_2`. In both branch proofs, split quantified index cases on `k = i`, used the same-index helper for the newly written cell, used the different-index helper for preserved prefix/suffix cells, and used `lia` for contradictory branch cases. For the exit witness, proved `i = n_pre` by arithmetic and chose `lr_2`.
- Result: the manual proof file now compiles and `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/array_copy_positive_proof_manual.v` produces no matches.

## Issue 5: first manual proof compile used the wrong bullet order after `entailer!`

- Phenomenon: the first compile of `array_copy_positive_proof_manual.v` failed with:

```text
File ".../array_copy_positive_proof_manual.v", line 93, characters 4-32:
Error: Found no subterm matching
"Zlength (replace_Znth ?M10553 ?M10554 ?M10555)" in the current goal.
```

- Trigger: after `Exists (...)` and the first `entailer!`, the script assumed the first remaining subgoal was the `Zlength (replace_Znth ...)` equality. Inspecting with `coqtop` showed that a second `entailer!` was needed, and the remaining subgoal order was suffix relation, nonpositive prefix relation, positive prefix relation, then length.
- Localization: `proof_of_array_copy_positive_entail_wit_2_1` and the analogous `proof_of_array_copy_positive_entail_wit_2_2` in `coq/generated/array_copy_positive_proof_manual.v`.
- Fix action: changed both proofs to:

```coq
Exists (...).
entailer!.
entailer!.
```

then reordered bullets to prove the suffix preservation first, the two prefix implications next, and the length equality last.
- Result: the fail-fast compile replay then compiled `array_copy_positive_proof_manual.v` and `array_copy_positive_goal_check.v` successfully.

## Issue 6: full compile and cleanup were required after proof success

- Phenomenon: successful `symexec` and successful manual proof are not sufficient for Verify success. The generated `goal`, `proof_auto`, `proof_manual`, and `goal_check` files must compile together under the workspace logical path, and non-`.v` Coq intermediates must be removed.
- Trigger: Coq compilation produces `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated`.
- Localization: `logs/compile.log` and `coq/generated/`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the documented base load paths and `-Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260422_025204_array_copy_positive`. There was no `original/array_copy_positive.v`, so the optional original compile was skipped. After compile success, removed every non-`.v` file under `coq/`.
- Result: `logs/compile.log` records:

```text
compile_start: 2026-04-22T02:57:09+08:00
skip original/array_copy_positive.v: not present
compile array_copy_positive_goal.v
compile array_copy_positive_proof_auto.v
compile array_copy_positive_proof_manual.v
compile array_copy_positive_goal_check.v
compile_end: 2026-04-22T02:57:13+08:00
```

After cleanup, `find coq -type f ! -name '*.v' -print` produced no output.
