# Issues

## Issue 1: workspace fingerprint started with empty semantic metadata

- Symptom: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and `"keywords": {}` even though the verify workflow requires non-empty retrieval metadata early in the task.
- Trigger: initial workspace bootstrap created a placeholder fingerprint before any task-specific analysis.
- Location: `logs/workspace_fingerprint.json`.
- Relevant initial fragment:

```json
"semantic_description": "",
"keywords": {}
```

- Fix: read the repository-level `doc/retrieval/INDEX.md` because the workspace itself did not contain `doc/`, then filled `semantic_description` with the read-only adjacent-pair scan semantics. Keywords were restricted to controlled vocabulary entries such as `algorithm_family: search`, `control_flow: ["for_loop", "if"]`, `data_shape: ["array", "pointer"]`, and after successful compile `verification_status: goal_check_passed`.
- Result: the fingerprint is non-empty and uses only controlled key/value names from the retrieval index.

## Issue 2: the raw loop needed a prefix invariant that allows the `n == 0` skip-loop case

- Symptom: the active annotated file initially matched the raw input and had no invariant before `for (i = 1; i < n; ++i)`.
- Trigger: `symexec` needs a loop-head assertion describing already checked adjacent pairs and preserving `IntArray::full`. A naive bound `i <= n` would be false immediately after `i = 1` when `n == 0`, even though the C loop correctly skips the body.
- Location: `annotated/verify_20260422_052907_array_is_strictly_increasing.c`.
- Relevant added annotation:

```c
/*@ Inv
      1 <= i && i <= n@pre + 1 &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (1 <= j && j < i) => l[j - 1] < l[j]) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 1; i < n; ++i) {
```

- Fix: wrote the invariant as a checked-prefix property over adjacent endpoints `j < i`, carried parameter equalities and array ownership, and used the `i <= n@pre + 1` boundary required by the `for` initializer before the loop guard.
- Result: `symexec` completed successfully. `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 3: the normal return path required an assertion-level disjunction proof

- Symptom: generated `coq/generated/array_is_strictly_increasing_proof_manual.v` contained one placeholder:

```coq
Lemma proof_of_array_is_strictly_increasing_return_wit_2 : array_is_strictly_increasing_return_wit_2.
Proof. Admitted.
```

- Trigger: the `return 1` VC must choose the right side of the postcondition disjunction and prove the universal strict-increase property for all `j < n_pre` from the invariant fact for all `j < i_3` plus the loop-exit fact `i_3 >= n_pre`.
- Location: `coq/generated/array_is_strictly_increasing_goal.v`, definition `array_is_strictly_increasing_return_wit_2`; proof in `coq/generated/array_is_strictly_increasing_proof_manual.v`.
- Relevant final proof:

```coq
Lemma proof_of_array_is_strictly_increasing_return_wit_2 : array_is_strictly_increasing_return_wit_2.
Proof.
  pre_process.
  Intros.
  Right.
  entailer!.
  intros j [? ?].
  apply H3.
  lia.
Qed.
```

- Fix: used `Right` for the QCP assertion-level disjunction, then proved the universal pure condition by applying the invariant's quantified hypothesis and discharging the index inequality with `lia`.
- Result: `proof_manual.v` no longer contains `Admitted.` or any newly added `Axiom`, and the full compile chain passed.

## Issue 4: compile products had to be removed after successful checking

- Symptom: successful `coqc` runs created `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files in `coq/generated/`.
- Trigger: Coq compilation writes intermediate artifacts next to each generated `.v` file.
- Location: `coq/generated/`.
- Fix: after `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` compiled successfully, removed all non-`.v` files under `coq/`.
- Result: `find coq -type f` now lists only:

```text
coq/generated/array_is_strictly_increasing_goal.v
coq/generated/array_is_strictly_increasing_goal_check.v
coq/generated/array_is_strictly_increasing_proof_auto.v
coq/generated/array_is_strictly_increasing_proof_manual.v
```
