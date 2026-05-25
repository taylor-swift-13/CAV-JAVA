## 2026-04-22 09:28 +0800 - Workspace fingerprint initialized from controlled retrieval vocabulary

- Phenomenon: `logs/workspace_fingerprint.json` was still at the script placeholder state: `semantic_description` was empty and `keywords` was `{}`.
- Trigger: verify workflow requires reading `doc/retrieval/INDEX.md` early and filling retrieval metadata using only the controlled key/value vocabulary.
- Localization: `output/verify_20260422_092628_binary_search_first/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, described the function as a read-only lower-bound binary search over a sorted `IntArray`, and filled controlled keywords:

```json
"keywords": {
  "algorithm_family": "search",
  "control_flow": ["while_loop", "if"],
  "data_shape": ["array", "pointer"],
  "semantic_intent": "preserve_input",
  "proof_pattern": ["loop_invariant", "case_split", "termination_by_bound", "monotonicity", "range_bound", "heap_reasoning"],
  "numeric_properties": ["nonnegative_input", "int_range"],
  "edge_case_behavior": ["empty_loop_possible", "branch_on_order"]
}
```

- Result: the fingerprint became useful for retrieval and was later extended with `verification_status: ["goal_check_passed", "proof_check_passed"]` after full verification succeeded.

## 2026-04-22 09:28 +0800 - Missing lower-bound loop invariant

- Phenomenon: the active annotated C initially matched the input and had no `Inv` or bridge `Assert` for the loop:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

- Trigger: the postcondition requires first occurrence or global absence of `target`. Without a loop invariant, symbolic execution has no persistent fact saying which indices are already known below `target` and which indices are known at least `target`.
- Localization: `annotated/verify_20260422_092628_binary_search_first.c`, immediately before `while (left < right)`.
- Fix action: added a half-open lower-bound invariant:

```c
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      0 <= left && left <= right && right <= n &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      (forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
      (forall (i: Z), (right <= i && i < n) => target <= l[i]) &&
      IntArray::full(a, n, l)
*/
```

This invariant records that `[0,left)` is strictly below `target`, `[right,n)` is at least `target`, and the input array resource and parameters are preserved.

- Result: the invariant gave the final `left == right` loop-exit state enough semantic information to prove both the first-occurrence return and the not-found return.

## 2026-04-22 09:28 +0800 - Midpoint bounds needed before array read and branch preservation

- Phenomenon: the assignment `mid = left + (right - left) / 2` must establish several facts before `a[mid]` can be read and before either branch can re-establish the invariant.
- Trigger: under `left < right`, the verifier needs explicit proof that `0 <= mid`, `mid < n`, `left <= mid`, and `mid < right`.
- Localization: `annotated/verify_20260422_092628_binary_search_first.c`, immediately after the midpoint assignment.
- Fix action: added a bridge assertion:

```c
/*@ Assert
      0 <= left && left < right && right <= n &&
      0 <= mid && mid < n &&
      left <= mid && mid < right &&
      ...
      IntArray::full(a, n, l)
*/
```

- Result: `symexec` generated the expected midpoint arithmetic witness `binary_search_first_entail_wit_2` and branch-preservation witnesses instead of failing at the array read or loop update.

## 2026-04-22 09:28 +0800 - Fresh symbolic execution required after annotation edits

- Phenomenon: the workspace initially had no generated Coq files for the edited annotated C, and verify rules require regenerating after every annotation change.
- Trigger: added `Inv` and `Assert` to the active annotated file.
- Localization: `logs/qcp_run.log`.
- Fix action: created `coq/generated/`, cleared stale generated targets if present, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_092628_binary_search_first.c \
  --goal-file=output/verify_20260422_092628_binary_search_first/coq/generated/binary_search_first_goal.v \
  --proof-auto-file=output/verify_20260422_092628_binary_search_first/coq/generated/binary_search_first_proof_auto.v \
  --proof-manual-file=output/verify_20260422_092628_binary_search_first/coq/generated/binary_search_first_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_092628_binary_search_first \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function binary_search_first
Successfully finished symbolic execution
symexec_end=2026-04-22 09:28:33 +0800
symexec_status=0
```

Fresh `binary_search_first_goal.v`, `binary_search_first_proof_auto.v`, `binary_search_first_proof_manual.v`, and `binary_search_first_goal_check.v` were generated.

## 2026-04-22 09:28 +0800 - Manual proof obligations remained after symexec

- Phenomenon: `coq/generated/binary_search_first_proof_manual.v` contained six admitted witnesses:

```coq
Lemma proof_of_binary_search_first_safety_wit_2 : binary_search_first_safety_wit_2.
Proof. Admitted.
...
Lemma proof_of_binary_search_first_return_wit_2 : binary_search_first_return_wit_2.
Proof. Admitted.
```

- Trigger: midpoint quotient bounds and sorted-array preservation facts are pure Coq obligations not solved automatically.
- Localization: `output/verify_20260422_092628_binary_search_first/coq/generated/binary_search_first_proof_manual.v`.
- Fix action: added local helper `binary_search_first_quot2_bounds`, proved midpoint safety and `entail_wit_2` with `Z.quot_pos` / `Z.quot_lt`, proved branch preservation with sortedness, and proved the `return -1` witness by selecting the assertion-level right disjunct:

```coq
assert (Hleft_eq_right: left = right) by lia.
assert (Hnot_found:
  forall j, 0 <= j < n_pre -> Znth j l 0 <> target_pre).
...
Right.
entailer!.
```

- Result: `binary_search_first_proof_manual.v` compiled successfully and `rg -n "Admitted\\.|^\\s*Axiom\\b"` on that file returned no matches.

## 2026-04-22 09:28 +0800 - Full compile replay and cleanup

- Phenomenon: successful `symexec` and manual proof compilation are not sufficient; verify completion requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting non-`.v` Coq artifacts.
- Trigger: normal verify completion criteria.
- Localization: `output/verify_20260422_092628_binary_search_first/coq/generated/`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the base `_CoqProject` load paths plus:

```bash
-Q output/verify_20260422_092628_binary_search_first/original ""
-R output/verify_20260422_092628_binary_search_first/coq/generated SimpleC.EE.CAV.verify_20260422_092628_binary_search_first
```

The compile order was `binary_search_first_goal.v`, `binary_search_first_proof_auto.v`, `binary_search_first_proof_manual.v`, and `binary_search_first_goal_check.v`.

- Result: all four generated Coq files compiled successfully. After `find coq -type f ! -name '*.v' -delete`, a follow-up `find coq -type f ! -name '*.v'` returned no files.
