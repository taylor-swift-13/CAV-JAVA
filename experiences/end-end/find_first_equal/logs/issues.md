# Verify issues

## Fingerprint placeholder filled before verification

- Phenomenon: the workspace fingerprint started with an empty semantic summary and empty keywords:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early, then replacing placeholder values with a non-empty `semantic_description` and controlled-vocabulary `keywords`.
- Location: `output/verify_20260422_165724_find_first_equal/logs/workspace_fingerprint.json`.
- Fix action: filled the semantic description with the actual behavior of `find_first_equal`: a read-only left-to-right scan over `a[0..n)` returning the first index whose value equals `k`, or `-1` when no such index exists. Used only controlled values such as `algorithm_family: search`, `control_flow: [for_loop, if]`, `data_shape: [array, pointer]`, `semantic_intent: preserve_input`, `proof_pattern: [loop_invariant, case_split, range_bound]`, `numeric_properties: int_range`, `edge_case_behavior: empty_loop_possible`, and after successful verification `verification_status: [goal_check_passed, proof_check_passed]`.
- Result: the fingerprint is non-empty and can be used for future retrieval.

## Missing scan invariant for first-match semantics

- Phenomenon: the active annotated file initially had no `Inv` before the loop and no loop-exit assertion before `return -1`.
- Trigger: both return paths require scan history. The in-loop return must prove that the returned `i` is the first matching index, not merely a matching index; the final `return -1` must prove every index in `[0,n)` is different from `k`.
- Location: `annotated/verify_20260422_165724_find_first_equal.c`, around the only `for (i = 0; i < n; ++i)` loop.
- Fix action: after writing detailed reasoning in `logs/annotation_reasoning.md`, added a loop invariant that preserves the array heap and unchanged parameters while accumulating the processed-prefix fact:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

- Fix action: added a minimal assertion immediately after loop exit to expose `i == n` and restate the no-match fact over the full range:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
return -1;
```

- Result: a fresh `symexec` run succeeded on the edited annotated file and generated `find_first_equal_goal.v`, `find_first_equal_proof_auto.v`, `find_first_equal_proof_manual.v`, and `find_first_equal_goal_check.v`.

Relevant `logs/qcp_run.log` ending:

```text
Symbolic Execution into function find_first_equal
End of symbolic execution of function find_first_equal
Successfully finished symbolic execution
symexec_status: 0
```

## Manual proof phase had no editable obligations

- Phenomenon: after successful symbolic execution, `output/verify_20260422_165724_find_first_equal/coq/generated/find_first_equal_proof_manual.v` contained only imports and scope openings.
- Trigger: all generated obligations for this simple read-only array scan were discharged through generated goal/auto artifacts; there was no `Lemma`, `Theorem`, or `Admitted.` in the manual file to edit.
- Fix action: skipped `logs/proof_reasoning.md` and did not edit `proof_manual.v`, because there was no concrete theorem, subgoal, tactic failure, or manual witness to analyze.
- Result: `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/find_first_equal_proof_manual.v` produced no matches.

Manual file shape:

```coq
From SimpleC.EE.CAV.verify_20260422_165724_find_first_equal Require Import find_first_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
```

## Full compile replay and cleanup

- Phenomenon: successful `symexec` alone is not sufficient for Verify success. The workflow requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` with the documented load path, then removing non-`.v` Coq intermediates.
- Trigger: Coq compilation creates `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Location: `logs/compile.log` and `output/verify_20260422_165724_find_first_equal/coq/generated/`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the base `_CoqProject`-style `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_165724_find_first_equal`. There was no `original/find_first_equal.v`, so that optional compile was skipped. After successful `goal_check`, deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `goal`, `proof_auto`, `proof_manual`, and `goal_check` all compiled successfully; the final cleanup check `find coq -type f ! -name '*.v' -print` produced no output.

Relevant `logs/compile.log`:

```text
compile_start: 2026-04-22T17:00:14+08:00
skip original/find_first_equal.v: not present
compiled find_first_equal_goal.v
compiled find_first_equal_proof_auto.v
compiled find_first_equal_proof_manual.v
compiled find_first_equal_goal_check.v
compile_end: 2026-04-22T17:00:17+08:00
compile_elapsed: 3s
compile_status: 0
```
