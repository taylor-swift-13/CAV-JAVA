# Issues

## Summary

- Status: completed successfully.
- Target function: `array_all_zero`.
- Active annotated C: `annotated/verify_20260422_021757_array_all_zero.c`.
- Final generated Coq directory: `output/verify_20260422_021757_array_all_zero/coq/generated`.

## Issue 1: initial fingerprint metadata was still an empty placeholder

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and an empty `keywords` object.
- Trigger condition: this workspace had just been initialized and had not yet recorded the retrieval metadata required by the verify workflow.
- Localization: `output/verify_20260422_021757_array_all_zero/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md` and filled `semantic_description` with the function behavior: a read-only scan over `a[0..n)`, early return `0` on the first nonzero element, return `1` when the whole array is zero, and vacuous success for `n == 0`. The `keywords` were restricted to the controlled vocabulary, including `algorithm_family: search`, `control_flow: [for_loop, if]`, `data_shape: [array, pointer]`, `proof_pattern: [loop_invariant, case_split, heap_reasoning]`, and final `verification_status: goal_check_passed`.
- Result: the fingerprint is now non-empty and retrieval-compatible.

## Issue 2: the loop needed an invariant for the processed all-zero prefix

- Phenomenon: the active annotated file initially had no `Inv` before the scan loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] != 0) {
        return 0;
    }
}

return 1;
```

- Trigger condition: the postcondition has two semantic cases. The early `return 0` case needs an existential index where `l[i] != 0`; the final `return 1` case needs a universal fact that every index in `0 <= i < n` has value zero. Without a loop invariant, the verifier has no persistent fact describing the processed prefix.
- Localization: `annotated/verify_20260422_021757_array_all_zero.c`, immediately before `for (i = 0; i < n; ++i)`.
- Fix action: added a loop invariant that records bounds, unchanged parameters, the read-only full array resource, and the processed-prefix property:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] == 0) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] != 0) {
        return 0;
    }
}
```

- Why this fixes the VC shape: `i` is the next index to inspect. The false branch of `a[i] != 0` proves the current element is zero, extending the prefix property from `[0, i)` to `[0, i + 1)`. The true branch uses current `i` as the existential witness for the `return 0` postcondition. The array is read-only, so `IntArray::full(a, n, l)` is preserved.
- Result: the generated symbolic execution conditions included enough state for both the early return and normal loop continuation.

## Issue 3: the final return needed a loop-exit assertion in postcondition-facing form

- Phenomenon: after loop exit, the invariant gives a prefix fact over `j < i`, while the `return 1` postcondition expects a universal fact over `j < n`.
- Trigger condition: the verifier benefits from an explicit assertion at the real loop-exit point that combines `!(i < n)` with `i <= n` to expose `i == n`.
- Localization: `annotated/verify_20260422_021757_array_all_zero.c`, immediately after the loop and before `return 1`.
- Fix action: added:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] == 0) &&
      IntArray::full(a, n, l)
*/
return 1;
```

- Result: `symexec` completed successfully against the updated annotated file. `logs/qcp_run.log` contains:

```text
Start to symbolic execution on program : annotated/verify_20260422_021757_array_all_zero.c
Symbolic Execution into function array_all_zero
End of symbolic execution of function array_all_zero
Successfully finished symbolic execution
symexec_status=0
```

Fresh `array_all_zero_goal.v`, `array_all_zero_proof_auto.v`, `array_all_zero_proof_manual.v`, and `array_all_zero_goal_check.v` were generated.

## Issue 4: no manual Coq witness was required after generation

- Phenomenon: `array_all_zero_proof_manual.v` contained only imports and scope setup, with no generated theorem or lemma bodies and no `Admitted.` placeholders.
- Trigger condition: the invariant and exit assertion were strong enough for the generated automatic proof obligations; manual proof did not need to add any theorem body.
- Localization: `output/verify_20260422_021757_array_all_zero/coq/generated/array_all_zero_proof_manual.v`.
- Check action: ran `rg -n "^Axiom\\b|Admitted\\."` on `array_all_zero_proof_manual.v`; it produced no matches.
- Result: the manual proof file satisfies the workflow restriction: no `Admitted.` and no newly declared `Axiom`.

## Issue 5: Coq replay left compiled artifacts that had to be cleaned

- Phenomenon: compiling generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger condition: normal `coqc` compilation of `array_all_zero_goal.v`, `array_all_zero_proof_auto.v`, `array_all_zero_proof_manual.v`, and `array_all_zero_goal_check.v`.
- Localization: `output/verify_20260422_021757_array_all_zero/coq/generated/`.
- Fix action: removed every non-`.v` file under the current workspace `coq/` directory after the successful compile replay.
- Result: `find .../coq -type f ! -name '*.v'` returns no files.

## Final verification chain

- `symexec`: succeeded on the latest annotated file; see `logs/qcp_run.log`.
- `array_all_zero_goal.v`: compiled successfully.
- `array_all_zero_proof_auto.v`: compiled successfully.
- `array_all_zero_proof_manual.v`: compiled successfully and contains no `Admitted.` or new `Axiom`.
- `array_all_zero_goal_check.v`: compiled successfully.
- `coq/` cleanup: complete; only `.v` files remain.
