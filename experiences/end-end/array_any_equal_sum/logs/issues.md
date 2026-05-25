# Verify Issues

## Issue 1: workspace fingerprint initially had empty retrieval fields

Symptom:

```json
"semantic_description": "",
"keywords": {},
```

Trigger and location: at the start of the verify task, `logs/workspace_fingerprint.json` still contained script-initialized placeholders. The verify workflow requires this file to be filled early, after reading `doc/retrieval/INDEX.md`, and requires every keyword key/value to come from the controlled vocabulary in that index.

Fix: read `doc/retrieval/INDEX.md` and updated the fingerprint with a concrete semantic description of the read-only array search:

```json
"semantic_description": "Read-only array scan. The function computes target = x + y, then uses a for loop over indices 0 <= i < n. It returns 1 immediately if some array element equals target, and returns 0 after the loop only when every element in the array is unequal to target. The input array memory is preserved; n may be zero, in which case the loop is skipped and the function returns 0.",
"keywords": {
  "algorithm_family": "search",
  "control_flow": ["for_loop", "if"],
  "data_shape": ["array", "scalar_only"],
  "semantic_intent": "preserve_input",
  "proof_pattern": ["loop_invariant", "case_split", "heap_reasoning"],
  "numeric_properties": ["overflow_guard", "int_range"],
  "edge_case_behavior": "empty_loop_possible"
}
```

Result: the fingerprint no longer has empty placeholders and can be used for later retrieval.

## Issue 2: unannotated loop did not preserve the prefix no-match fact needed by `return 0`

Symptom: the active annotated file initially had no loop invariant or exit assertion:

```c
int i;
int target = x + y;

for (i = 0; i < n; ++i) {
    if (a[i] == target) {
        return 1;
    }
}

return 0;
```

Why this is a verification problem: the postcondition for `__return == 0` requires:

```c
forall (i: Z), (0 <= i && i < n) => l[i] != x + y
```

Without an invariant, symbolic execution has no persistent fact saying that all previously scanned indices differ from `target`. The `return 1` branch also needs the current index to satisfy `l[i] == x + y`, while the final `return 0` branch needs the processed-prefix fact expanded to the whole range after `i == n`.

Fix: before editing, recorded the invariant reasoning in `logs/annotation_reasoning.md`, then added a loop invariant to `annotated/verify_20260422_022338_array_any_equal_sum.c`:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      x == x@pre &&
      y == y@pre &&
      target == x + y &&
      INT_MIN <= target && target <= INT_MAX &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != target) &&
      IntArray::full(a, n, l)
*/
```

Also added a loop-exit assertion immediately after the loop:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      x == x@pre &&
      y == y@pre &&
      target == x + y &&
      INT_MIN <= target && target <= INT_MAX &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != target) &&
      IntArray::full(a, n, l)
*/
```

Result: reran `symexec` after the annotation change. `logs/qcp_run.log` ended with:

```text
Symbolic Execution into function array_any_equal_sum
End of symbolic execution of function array_any_equal_sum
Successfully finished symbolic execution
```

The run generated `array_any_equal_sum_goal.v`, `array_any_equal_sum_proof_auto.v`, `array_any_equal_sum_proof_manual.v`, and `array_any_equal_sum_goal_check.v` in the current workspace.

## Issue 3: Coq compilation creates non-source artifacts that must be cleaned after success

Symptom: after compiling the generated Coq files, `coq/generated/` contained `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files for the generated modules.

Trigger: normal `coqc` compilation of:

```text
array_any_equal_sum_goal.v
array_any_equal_sum_proof_auto.v
array_any_equal_sum_proof_manual.v
array_any_equal_sum_goal_check.v
```

Fix: after all compile steps passed, removed every non-`.v` file under the current workspace `coq/` directory.

Result: a final `find output/verify_20260422_022338_array_any_equal_sum/coq -type f ! -name '*.v'` returned no files.
