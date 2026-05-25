# Verify Issues

## 2026-04-22 01:43 CST - Workspace fingerprint placeholders had to be filled before proof work

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords` object.
- Trigger: the verify workflow requires the fingerprint to be made useful early in the task, and the user explicitly requested reading `doc/retrieval/INDEX.md` and using only its controlled vocabulary.
- Location: `output/verify_20260422_014304_array_add/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then populated `semantic_description` with the array elementwise-add semantics and used only controlled keys/values:

```json
"algorithm_family": "prefix_sum",
"control_flow": "for_loop",
"data_shape": "array",
"semantic_intent": "in_place_update",
"proof_pattern": ["loop_invariant", "heap_reasoning", "range_bound"],
"numeric_properties": ["overflow_guard", "int_range"],
"edge_case_behavior": "empty_loop_possible"
```

- Result: the fingerprint is non-empty and, after final `goal_check` success, also records `"verification_status": "goal_check_passed"`.

## 2026-04-22 01:44 CST - The unannotated loop needed a prefix/suffix output invariant

- Phenomenon: the active annotated file initially had the same unannotated loop as the input:

```c
for (i = 0; i < n; ++i) {
    out[i] = a[i] + b[i];
}
```

- Trigger: the postcondition needs an existential final list `lr` with every element equal to `la[i] + lb[i]`, but without a loop invariant there is no retained proof state describing which prefix of `out` has already been updated and which suffix still equals the original `lo`.
- Location: `annotated/verify_20260422_014304_array_add.c`, before and inside the `for` loop.
- Fix action: added a loop invariant with existential lists `l1` and `l2`, where `l1` is the processed prefix, `l2` is the untouched suffix, and `IntArray::full(out, n@pre, app(l1, l2))` preserves full ownership. Added bridge assertions before and after the assignment:

```c
IntArray::missing_i(out, i, 0, n@pre, app(l1, l2)) *
data_at(out + (i * sizeof(int)), int, lo[i])
```

and after the write:

```c
exists l1',
  Zlength(l1') == i + 1 &&
  (forall (k: Z), (0 <= k && k < i + 1) => l1'[k] == la[k] + lb[k]) &&
IntArray::full(out, n@pre, app(l1', sublist(i + 1, n@pre, lo)))
```

- Result: `symexec` generated fresh `array_add_goal.v`, `array_add_proof_auto.v`, `array_add_proof_manual.v`, and `array_add_goal_check.v`.

## 2026-04-22 01:45 CST - Symbolic execution succeeded

- Phenomenon: a clean symbolic execution run was required after adding `Inv` and `which implies` annotations.
- Trigger: the workflow requires regenerating Coq files after any annotation change and clearing stale generated files first.
- Location: `output/verify_20260422_014304_array_add/logs/qcp_run.log`.
- Fix action: removed any stale generated `array_add_*.v` files and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_014304_array_add.c \
  --goal-file=output/verify_20260422_014304_array_add/coq/generated/array_add_goal.v \
  --proof-auto-file=output/verify_20260422_014304_array_add/coq/generated/array_add_proof_auto.v \
  --proof-manual-file=output/verify_20260422_014304_array_add/coq/generated/array_add_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_014304_array_add \
  --no-exec-info
```

- Result: `qcp_run.log` ended with:

```text
End of symbolic execution of function array_add
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 01:47 CST - First manual proof compile wrapper did not fail fast

- Phenomenon: the first full compile log contained real `coqc` errors but still printed later `compiled ...` lines:

```text
Error:
 (in proof proof_of_array_add_safety_wit_2): Attempt to save an incomplete proof
(there are remaining open goals).

compiled array_add_proof_manual.v
Error: Cannot find a physical path bound to logical path
array_add_proof_manual with prefix SimpleC.EE.CAV.verify_20260422_014304_array_add.
compiled array_add_goal_check.v
```

- Trigger: the initial shell compile block did not use `set -e`, so it continued after failing `coqc` commands. The later `goal_check` error was a consequence of `array_add_proof_manual.vo` not being produced.
- Location: `output/verify_20260422_014304_array_add/logs/compile.log`, first overwritten compile attempt before the final fail-fast replay.
- Fix action: switched subsequent compile replay to a fail-fast shell with `set -e`, then fixed `proof_manual.v` before rerunning the full template.
- Result: the final `compile.log` only contains successful compile steps and a real `array_add_goal_check.v` success.

## 2026-04-22 01:47 CST - `array_add_safety_wit_2` needed explicit overflow-premise instantiation

- Phenomenon: replacing `Admitted.` with only `pre_process; entailer!` left two pure arithmetic goals:

```coq
-2147483648 <= Znth i la 0 + Znth i lb 0
Znth i la 0 + Znth i lb 0 <= 2147483647
```

- Trigger: `entailer!` did not automatically instantiate the contract premise:

```coq
H13 :
  forall i_2 : Z,
    0 <= i_2 < n_pre ->
    -2147483648 <= Znth i_2 la 0 + Znth i_2 lb 0 <= 2147483647
```

- Location: `array_add_safety_wit_2` in `coq/generated/array_add_proof_manual.v`.
- Fix action: instantiated `H13` at `i` in both subgoals:

```coq
pose proof (H13 i ltac:(lia)) as Hsum.
lia.
```

- Result: the safety witness compiled.

## 2026-04-22 01:48 CST - Loop invariant witnesses had to be supplied explicitly

- Phenomenon: `array_add_entail_wit_1` and `array_add_entail_wit_2` stayed open with existential goals for `l2` and `l1`.
- Trigger: these are assertion-level existentials in QCP separation-logic goals, so `entailer!` did not guess the intended prefix/suffix lists.
- Location: `array_add_entail_wit_1` and `array_add_entail_wit_2`.
- Fix action: used `Exists lo; Exists nil` for initialization, and `Exists (sublist (i_2 + 1) n_pre lo); Exists l1'` for preservation. The preservation proof also needed:

```coq
rewrite Znth_sublist by lia.
rewrite Zlength_sublist by lia.
```

- Result: both entailment witnesses compiled.

## 2026-04-22 01:49 CST - Return witness needed full-prefix normalization

- Phenomenon: `array_add_return_wit_1` remained an existential return-list goal after `pre_process; entailer!`.
- Trigger: the loop exit assumptions separately had `i_3 >= n_pre` and `i_3 <= n_pre`; Coq needed the equality before the prefix fact could be used for every postcondition index.
- Location: `array_add_return_wit_1`.
- Fix action: proved `i_3 = n_pre`, chose `lr = app l1 l2`, and used `app_Znth1` plus the invariant prefix relation:

```coq
assert (Hi : i_3 = n_pre) by lia.
subst i_3.
Exists (app l1 l2).
entailer!.
- intros i Hi_range.
  rewrite app_Znth1 by lia.
  apply H7; lia.
- rewrite Zlength_app.
  lia.
```

- Result: the return witness compiled.

## 2026-04-22 01:53 CST - Array bridge proofs needed direct split/merge lemmas and list normalization

- Phenomenon: both `array_add_which_implies_wit_1` and `array_add_which_implies_wit_2` stayed open under `pre_process; entailer!`.
- Trigger: these goals require explicit heap predicate transformations:
  - split `IntArray.full` into `IntArray.missing_i` plus a `data_at` cell;
  - merge updated `missing_i` predicates back into full arrays;
  - normalize the output list after writing index `i`.
- Location: `array_add_which_implies_wit_1` and `array_add_which_implies_wit_2`.
- Fix action for `which_implies_wit_1`: used `IntArray.full_split_to_missing_i` with default `0` for `a`, `b`, and `out`, then proved:

```coq
Znth i (app l1 l2) 0 = Znth i lo 0
```

using `app_Znth2`, `Zlength l1 = i`, and the suffix invariant at offset `0`.
- Fix action for `which_implies_wit_2`: first proved `l2 = sublist i n_pre lo` with `list_eq_ext`, chose `l1 ++ [Znth i la 0 + Znth i lb 0]` as the new prefix, merged all three arrays with `IntArray.missing_i_merge_to_full`, and normalized the resulting output list using `replace_Znth_app_r`, `sublist_split`, and `sublist_single`.
- Result: `array_add_proof_manual.v` compiled without `Admitted.` or local `Axiom`.

## 2026-04-22 01:55 CST - Final compile and cleanup succeeded

- Phenomenon: Verify completion requires a full compile replay and cleanup of generated Coq artifacts.
- Trigger: successful manual proof compilation alone is insufficient; `goal_check.v` must compile, and non-`.v` files under `coq/` must be removed afterward.
- Location: `output/verify_20260422_014304_array_add/coq/generated/` and `logs/compile.log`.
- Fix action: ran the full compile template from `QualifiedCProgramming/SeparationLogic` with `set -e`, compiling:

```text
array_add_goal.v
array_add_proof_auto.v
array_add_proof_manual.v
array_add_goal_check.v
```

Then removed non-`.v` files under `output/verify_20260422_014304_array_add/coq/`.
- Result: final `compile.log` ends with `compiled array_add_goal_check.v`; after cleanup, only the four generated `.v` files remain under `coq/generated/`.
