## 2026-04-22 09:14-09:22 +0800 - Workspace fingerprint was initialized with empty retrieval metadata

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` keywords, which violates the verify workflow and makes later retrieval ineffective.
- Trigger: initial workspace setup for `verify_20260422_091409_binary_search`.
- Localization: `output/verify_20260422_091409_binary_search/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and used only controlled vocabulary keys/values:

```json
"algorithm_family": "search",
"control_flow": ["while_loop", "if"],
"data_shape": ["array", "pointer"],
"semantic_intent": "preserve_input",
"proof_pattern": ["loop_invariant", "case_split", "range_bound", "monotonicity", "heap_reasoning"],
"numeric_properties": ["nonnegative_input", "overflow_guard", "int_range"],
"edge_case_behavior": ["branch_on_order", "empty_loop_possible"]
```

- Result: the fingerprint now describes iterative binary search over a sorted read-only integer array and, after final compilation, records `"verification_status": ["goal_check_passed", "proof_check_passed"]`.

## 2026-04-22 09:15-09:18 +0800 - Missing loop invariant and bridge assertion for binary-search interval

- Phenomenon: the active annotated C initially had no loop invariant for the `while (left <= right)` loop, so the verifier had no way to preserve the shrinking interval semantics needed for the `-1` return.
- Trigger: original loop body:

```c
while (left <= right) {
    mid = left + (right - left) / 2;
    if (a[mid] == target) {
        return mid;
    }
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid - 1;
    }
}
```

- Localization: `annotated/verify_20260422_091409_binary_search.c`.
- Fix action: added an invariant that preserves bounds, sortedness, parameter stability, `IntArray::full(a, n, l)`, and the two eliminated ranges:

```c
(forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
(forall (i: Z), (right < i && i < n) => target < l[i])
```

- Result: this gave the verification condition enough semantic information to prove that any index outside the remaining search interval cannot contain `target`.

## 2026-04-22 09:16 +0800 - First `symexec` command used wrong option syntax

- Phenomenon: the first manual `symexec` invocation failed immediately with:

```text
goal file not specified
Start to symbolic execution on program : (null)
symexec_status=1
```

- Trigger: command used space-separated long options such as `--goal-file coq/generated/binary_search_goal.v`, but this binary expects `--goal-file=/abs/path`.
- Localization: `logs/qcp_run.log` from the first attempt.
- Fix action: reran with the successful style used by existing examples:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_091409_binary_search.c \
  --goal-file=output/verify_20260422_091409_binary_search/coq/generated/binary_search_goal.v \
  --proof-auto-file=output/verify_20260422_091409_binary_search/coq/generated/binary_search_proof_auto.v \
  --proof-manual-file=output/verify_20260422_091409_binary_search/coq/generated/binary_search_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_091409_binary_search \
  --no-exec-info
```

- Result: the command-line issue was fixed; later `symexec` attempts parsed the annotated C.

## 2026-04-22 09:16-09:17 +0800 - `symexec` could not derive `mid` bounds for `a[mid]`

- Phenomenon: after adding the invariant, `symexec` failed at the first array read:

```text
fatal error: Cannot derive the precondition of Memory Read. in .../annotated/verify_20260422_091409_binary_search.c:44:8
```

- Trigger: the tool did not automatically derive `0 <= mid < n` from `mid = left + (right - left) / 2`, `0 <= left`, `left <= right`, and `right < n`.
- Localization: the read `if (a[mid] == target)`.
- Fix action: inserted a bridge assertion immediately after assigning `mid`, before the first read:

```c
/*@ Assert
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      ... sortedness and loop bounds ... &&
      0 <= mid && mid < n &&
      left <= mid && mid <= right &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      ... eliminated ranges ... &&
      IntArray::full(a, n, l)
*/
```

- Result: the memory-read precondition became derivable. A narrower first version of this bridge kept only `mid` bounds and `IntArray::full`, but failed because `Assert` acted as a cut and dropped the live `target` binding needed by the next comparison.

## 2026-04-22 09:17 +0800 - Post-loop assertion caused local permission cleanup failure for possibly uninitialized `mid`

- Phenomenon: after widening the `mid` bridge assertion, `symexec` reached the loop exit but failed at function cleanup:

```text
fatal error: Error: Fail to Remove Memory Permission of mid:106 in .../annotated/verify_20260422_091409_binary_search.c:85:4
Address found : null
```

- Trigger: a post-loop `Assert` before `return -1` omitted the local `mid`, but `mid` is declared before the loop and can be uninitialized if the loop is skipped, for example when `n == 0`.
- Localization: post-loop assertion before `return -1`.
- Fix action: removed the post-loop assertion and relied on the loop invariant plus negated loop condition for the final return witness.
- Result: the next clean `symexec` run succeeded:

```text
End of symbolic execution of function binary_search
Successfully finished symbolic execution
symexec_status=0
```

It generated fresh `binary_search_goal.v`, `binary_search_proof_auto.v`, `binary_search_proof_manual.v`, and `binary_search_goal_check.v`.

## 2026-04-22 09:18-09:21 +0800 - Manual proof needed quotient bounds and explicit sortedness instantiation

- Phenomenon: generated `coq/generated/binary_search_proof_manual.v` contained five admitted obligations: `safety_wit_4`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3_1`, and `entail_wit_3_2`.
- Trigger: midpoint arithmetic uses C-style quotient `(right - left) ÷ 2`, and branch invariant preservation requires sortedness facts that automation does not instantiate by itself.
- Localization: `output/verify_20260422_091409_binary_search/coq/generated/binary_search_proof_manual.v`.
- First failed proof attempt:

```coq
Proof.
  pre_process.
  entailer!.
  lia.
Qed.
```

failed with:

```text
Error: Tactic failure: Cannot find witness.
```

- Fix action: added a local quotient helper:

```coq
Lemma binary_search_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
```

Then used it in `safety_wit_4` and `entail_wit_2`. For `entail_wit_3_1`, added a local fact:

```coq
forall j, mid <= j < n_pre -> target_pre < Znth j l 0
```

and for `entail_wit_3_2`, added:

```coq
forall j, 0 <= j < mid + 1 -> Znth j l 0 < target_pre
```

Both facts use the sortedness hypothesis from the invariant and the current branch comparison result. The branch proofs also call `sep_apply store_int_undef_store_int` so the concrete `mid` cell can match the invariant's undefined `mid` cell.
- Result: `binary_search_proof_manual.v` compiles, contains no `Admitted.`, and contains no new `Axiom`.

## 2026-04-22 09:21 +0800 - Full Coq compile and cleanup

- Phenomenon: verify completion requires more than successful `symexec` and manual proof compilation; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must all compile with the stable load path.
- Trigger: final compile replay from `QualifiedCProgramming/SeparationLogic`.
- Fix action: compiled in order with the `COMPILE.md` template:

```text
compiled=binary_search_goal.v
compiled=binary_search_proof_auto.v
compiled=binary_search_proof_manual.v
compiled=binary_search_goal_check.v
```

- Result: all required Coq files compiled successfully. Non-`.v` generated artifacts were then removed from `coq/generated/`.

## 2026-04-22 09:22 +0800 - Experience update decision

- Phenomenon: this task exposed a reusable proof pattern for midpoint quotient bounds and sortedness preservation around binary search.
- Trigger: the workflow normally asks for reusable experience updates.
- Constraint: the user explicitly required “Work only inside this existing workspace,” and repository-level `experiences/*.md` files are outside this workspace.
- Fix action: did not modify repository-level experience documents. The reusable details were recorded in this workspace's `annotation_reasoning.md`, `proof_reasoning.md`, and this `issues.md`.
- Result: `metrics.md` records `Experience updates: none`.
