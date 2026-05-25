## Fingerprint Backfill

- Phenomenon: the initialized workspace fingerprint had an empty `semantic_description` and `{}` for `keywords`, which is not usable for retrieval handoff.
- Trigger: `logs/workspace_fingerprint.json` initially contained:

```json
"semantic_description": "",
"keywords": {}
```

- Fix action: read `doc/retrieval/INDEX.md` early in the task and filled a description of the read-only adjacent-pair sortedness scan. The keyword keys and values were restricted to the controlled vocabulary, including `algorithm_family: search`, `control_flow: ["for_loop", "if"]`, `data_shape: ["array", "pointer"]`, and final `verification_status` values after compile replay passed.
- Result: the fingerprint now has a non-empty semantic description and controlled keywords suitable for future retrieval.

## Missing Initial Loop Invariant

- Phenomenon: the active annotated C initially matched `input/is_sorted_nondecreasing.c` and had no `Inv` before the loop:

```c
for (i = 0; i + 1 < n; ++i) {
    if (a[i] > a[i + 1]) {
        return 0;
    }
}
return 1;
```

- Trigger: without a loop invariant, symbolic execution has no reusable state saying all already scanned adjacent pairs are nondecreasing and no explicit preserved `IntArray::full(a, n, l)` ownership for either return branch.
- Fix action: added a loop invariant in `annotated/verify_20260422_181654_is_sorted_nondecreasing.c` that tracks bounds, unchanged parameters, heap ownership, and the processed-prefix fact:

```c
/*@ Inv
      0 <= i && i <= n &&
      (0 < n => i + 1 <= n) &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] <= l[j + 1]) &&
      IntArray::full(a, n, l)
*/
```

- Result: after regenerating with `symexec`, the only manual proof obligation left was the normal return witness `proof_of_is_sorted_nondecreasing_return_wit_2`.

## Loop Guard Range Bound

- Phenomenon: the first invariant omitted `(0 < n => i + 1 <= n)`. `symexec` succeeded, but `coq/generated/is_sorted_nondecreasing_proof_manual.v` contained `proof_of_is_sorted_nondecreasing_safety_wit_2`; compiling the first proof attempt failed with:

```text
Error:
 (in proof proof_of_is_sorted_nondecreasing_safety_wit_2):
 Attempt to save an incomplete proof
```

- Trigger: a `coqtop` probe showed the remaining goal was:

```coq
i + 1 <= 2147483647
```

with only `0 <= i`, `i <= n_pre`, and `0 <= n_pre` available as pure facts. The input contract does not state `n <= INT_MAX`, so the original invariant was too weak for the C integer safety of evaluating `i + 1`.
- Fix action: followed the documented `i + 1 < n` scan-loop pattern and added the conditional source-level bound `(0 < n => i + 1 <= n)` instead of adding an uninitializable `n <= INT_MAX` invariant conjunct. Cleared generated Coq files and reran `symexec`.
- Result: the regenerated manual proof file no longer contained the safety witness; it contained only the return witness.

## Compile Replay Must Be Fail-Fast

- Phenomenon: the first batch compile script did not use fail-fast shell behavior, so it echoed later `compiled=...:success` lines after `coqc` had already failed.
- Trigger: `logs/compile_full.log` from the first replay included an error for `proof_manual.v` followed by misleading success echoes.
- Fix action: reran compile replay with `set -e` inside the logged command block. The final `logs/compile_full.log` now records only successful compile steps:

```text
compiled=is_sorted_nondecreasing_goal.v:success
compiled=is_sorted_nondecreasing_proof_auto.v:success
compiled=is_sorted_nondecreasing_proof_manual.v:success
compiled=is_sorted_nondecreasing_goal_check.v:success
```

- Result: `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` compiled under the workspace load path, and non-`.v` Coq intermediates were removed afterward.

## Manual Return Witness

- Phenomenon: after the final `symexec`, `coq/generated/is_sorted_nondecreasing_proof_manual.v` contained one generated placeholder:

```coq
Lemma proof_of_is_sorted_nondecreasing_return_wit_2 : is_sorted_nondecreasing_return_wit_2.
Proof. Admitted.
```

- Trigger: the normal return postcondition needs the full adjacent-pair universal property, while the invariant stores it only for processed indices `j < i_3`. The loop-exit fact `i_3 + 1 >= n_pre` must bridge a target index satisfying `j + 1 < n_pre` into `j < i_3`.
- Fix action: replaced the placeholder with an assertion-level right-branch proof:

```coq
Proof.
  pre_process.
  Right.
  entailer!.
  intros.
  apply H3.
  lia.
Qed.
```

- Result: the manual proof compiled, `goal_check.v` compiled, and `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
