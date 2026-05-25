# Verify issues

## Fingerprint placeholder had to be filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` still contained the initialization placeholder state: `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and replacing placeholders before proof work continues. The controlled vocabulary in that file is the only allowed source for keyword keys and values.
- Location: `output/verify_20260422_024651_array_contains/logs/workspace_fingerprint.json`.
- Fix action: filled `semantic_description` with the task semantics: a read-only integer-array search over `a[0..n)` that returns `1` on a matching element and returns `0` only after every index in range is known not to equal `k`. Used only controlled keys and values such as `algorithm_family: search`, `control_flow: [for_loop, if]`, `data_shape: [array, pointer]`, `proof_pattern: [loop_invariant, case_split, termination_by_bound, heap_reasoning]`, and `edge_case_behavior: empty_loop_possible`.
- Result: the fingerprint is now non-empty and, after `goal_check` passed, also records `verification_status: [goal_check_passed, proof_check_passed]`.

Relevant before state:

```json
"semantic_description": "",
"keywords": {}
```

Relevant after state:

```json
"semantic_description": "array_contains scans the input integer array a[0..n) with a for loop, does not modify memory, returns 1 immediately when some element equals k, and returns 0 only after the loop has established that every index in the range is not equal to k. The empty-loop case n == 0 is allowed and returns 0 while preserving IntArray::full(a, n, l).",
"keywords": {
  "algorithm_family": "search",
  "control_flow": ["for_loop", "if"],
  "data_shape": ["array", "pointer"],
  "semantic_intent": "preserve_input",
  "proof_pattern": ["loop_invariant", "case_split", "termination_by_bound", "heap_reasoning"],
  "numeric_properties": ["nonnegative_input", "int_range"],
  "edge_case_behavior": "empty_loop_possible",
  "verification_status": ["goal_check_passed", "proof_check_passed"]
}
```

## Missing loop invariant for read-only array search

- Phenomenon: the active annotated file initially had no `Inv` before the `for (i = 0; i < n; ++i)` loop and no exit assertion before `return 0`.
- Trigger: the postcondition has two semantic branches. The early `return 1` branch needs an existential witness index where `l[i] == k`; the final `return 0` branch needs the universal fact that all indices in `[0,n)` are different from `k`. Without a loop invariant, symbolic execution has no stable fact storing the already scanned prefix and no explicit unchanged-parameter facts for returning the same `IntArray::full(a, n, l)` resource.
- Location: `annotated/verify_20260422_024651_array_contains.c`, around the only loop.
- Fix action: after recording detailed reasoning in `logs/annotation_reasoning.md`, added a prefix invariant that keeps `0 <= i <= n`, unchanged `a`, `n`, and `k`, the read-only heap predicate, and the processed-prefix fact `(forall (j: Z), (0 <= j && j < i) => l[j] != k)`. Added a minimal loop-exit assertion converting loop exit to `i == n` and restating the universal prefix fact over `[0,n)`.
- Result: rerunning `symexec` against the updated annotated file succeeded and generated fresh `array_contains_goal.v`, `array_contains_proof_auto.v`, `array_contains_proof_manual.v`, and `array_contains_goal_check.v`.

Initial C shape:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        return 1;
    }
}

return 0;
```

Final annotation shape:

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
    if (a[i] == k) {
        return 1;
    }
}

/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
return 0;
```

Relevant `symexec` result from `logs/qcp_run.log`:

```text
Start to symbolic execution on program : annotated/verify_20260422_024651_array_contains.c
Symbolic Execution into function array_contains
End of symbolic execution of function array_contains
Successfully finished symbolic execution
symexec_status: 0
```

## Manual proof phase had no editable obligations

- Phenomenon: after successful `symexec`, `coq/generated/array_contains_proof_manual.v` contained only imports and scope openings. It had no `Lemma`, `Theorem`, or `Admitted.` body to fill.
- Trigger: all generated witness lemmas for this simple scan were placed in `array_contains_proof_auto.v`; the manual file did not contain any task-specific proof obligation.
- Location: `output/verify_20260422_024651_array_contains/coq/generated/array_contains_proof_manual.v`.
- Fix action: skipped manual proof editing and did not create `logs/proof_reasoning.md`, because there was no failed theorem, remaining subgoal, or proof script to analyze before editing.
- Result: `rg -n "Admitted\\.|^\\s*Axiom\\b" .../array_contains_proof_manual.v` produced no matches, and the full compile replay compiled `array_contains_proof_manual.v` and `array_contains_goal_check.v` successfully.

Relevant manual file shape:

```coq
From SimpleC.EE.CAV.verify_20260422_024651_array_contains Require Import array_contains_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
```

## Full compile replay and cleanup

- Phenomenon: `symexec` success alone is not the completion condition; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must compile under the documented load-path template, and non-`.v` Coq intermediates must be removed afterward.
- Trigger: compiling Coq generated `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Location: `output/verify_20260422_024651_array_contains/coq/generated/`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with `_CoqProject`-equivalent base `-R` arguments and extra workspace paths `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_024651_array_contains`. There was no `original/array_contains.v`, so that optional compile step was skipped. After successful `goal_check`, deleted every non-`.v` file under `coq/`.
- Result: `array_contains_goal.v`, `array_contains_proof_auto.v`, `array_contains_proof_manual.v`, and `array_contains_goal_check.v` all compiled successfully. A final `find output/verify_20260422_024651_array_contains/coq -type f ! -name '*.v' -print` produced no output.

Relevant compile log:

```text
compile_start: 2026-04-22T02:48:57+08:00
skip original/array_contains.v: not present
compile array_contains_goal.v
compile array_contains_proof_auto.v
compile array_contains_proof_manual.v
compile array_contains_goal_check.v
compile_end: 2026-04-22T02:48:59+08:00
```
