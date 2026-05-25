## Issue 1: Workspace fingerprint initially had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and empty `keywords`, which makes the workspace unusable for later retrieval.
- Trigger: the initialized workspace contained only placeholder retrieval fields:

```json
"semantic_description": "",
"keywords": {}
```

- Fix action: read `doc/retrieval/INDEX.md` and filled the fingerprint with a semantic description of the read-only adjacent-pair scan. The keyword keys and values were chosen only from the controlled vocabulary: `algorithm_family=search`, `control_flow=[for_loop, if]`, `data_shape=[array, pointer]`, `semantic_intent=preserve_input`, `proof_pattern=[loop_invariant, case_split, range_bound, heap_reasoning]`, `numeric_properties=[nonnegative_input, int_range]`, `edge_case_behavior=empty_loop_possible`, and final `verification_status=[goal_check_passed, proof_check_passed, auto_proof_contains_admitted, generated_goal_contains_axioms]`.
- Result: the fingerprint is non-empty and records both the task semantics and final verification status.

## Issue 2: The loop needed a prefix invariant that allows skip-loop cases

- Phenomenon: the active annotated C initially copied the input C exactly and had no loop invariant before `for (i = 1; i < n; ++i)`. Without an invariant, `symexec` would not know that all previously scanned adjacent pairs are unequal when proving the `return 0` postcondition.
- Trigger: the contract permits `n == 0` and `n == 1`, so a simple bound like `i <= n` is false immediately after `i = 1` when `n == 0`.
- Fix action: added this invariant in `annotated/verify_20260422_045045_array_has_adjacent_equal.c`:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1]) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
    if (a[i] == a[i - 1]) {
        return 1;
    }
}
```

- Result: the invariant captures the processed prefix `1 <= j < i`, preserves the unchanged input array, supports early return with witness `i`, and remains initialized for `n == 0`.

## Issue 3: A too-late loop-exit assertion caused local permission cleanup failure

- Phenomenon: the first `symexec` run after adding an explicit assertion before `return 0` failed with:

```text
fatal error: Error: Fail to Remove Memory Permission of i:96 in
annotated/verify_20260422_045045_array_has_adjacent_equal.c:40:4
Address found : nullCurrent assertion is :
symexec_status=1
```

- Trigger: the assertion was placed after the loop and immediately before return:

```c
/*@ Assert
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (1 <= j && j < n) => l[j] != l[j - 1]) &&
      IntArray::full(a, n, l)
*/
return 0;
```

This matched the known pattern where a loop-exit assertion placed too late can interfere with removing a local variable permission.
- Fix action: removed the explicit loop-exit assertion and kept the loop invariant unchanged. The return witness can derive the postcondition directly from the invariant and the loop-exit guard fact `i_3 >= n_pre`.
- Result: rerunning `symexec` against the updated annotated file succeeded. `logs/qcp_run.log` ends with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T04:52:58+08:00
symexec_status=0
```

Fresh generated files were produced: `array_has_adjacent_equal_goal.v`, `array_has_adjacent_equal_proof_auto.v`, `array_has_adjacent_equal_proof_manual.v`, and `array_has_adjacent_equal_goal_check.v`.

## Issue 4: Manual proof was needed for the zero-return witness

- Phenomenon: after successful `symexec`, `coq/generated/array_has_adjacent_equal_proof_manual.v` contained one admitted manual lemma:

```coq
Lemma proof_of_array_has_adjacent_equal_return_wit_2 :
  array_has_adjacent_equal_return_wit_2.
Proof. Admitted.
```

- Trigger: the generated return witness had to prove the postcondition universal from the invariant universal and the loop-exit guard:

```coq
[| (i_3 >= n_pre) |] &&
[| forall j,
     1 <= j /\ j < i_3 ->
     Znth j l 0 <> Znth (j - 1) l 0 |]
|--
[| forall i,
     1 <= i /\ i < n_pre ->
     Znth i l 0 <> Znth (i - 1) l 0 |] && ...
```

- Fix action: replaced the admitted proof with an assertion-level left-disjunct proof. The proof keeps the heap with `entailer!`, introduces the target index, applies the invariant universal, and uses `lia` to bridge `i < n_pre` and `n_pre <= i_3` into `i < i_3`:

```coq
Proof.
  pre_process.
  Left.
  entailer!.
  intros i [? ?].
  match goal with
  | H : forall j : Z, 1 <= j /\ j < _ -> _ |- _ =>
      apply H; lia
  end.
Qed.
```

- Result: `array_has_adjacent_equal_proof_manual.v` compiles and contains no `Admitted.` or locally added `Axiom`.

## Issue 5: Verification required full compile replay and Coq artifact cleanup

- Phenomenon: successful `symexec` and manual proof are not sufficient by themselves; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must compile under the workspace load path, and generated non-`.v` Coq artifacts must be removed.
- Trigger: normal Coq compilation creates `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the documented base `-R` arguments and workspace paths `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_045045_array_has_adjacent_equal`. There was no `original/array_has_adjacent_equal.v`, so the optional original compile was skipped. After `goal_check` passed, deleted all non-`.v` files under the current workspace `coq/`.
- Result: `logs/compile_full.log` records:

```text
compiled=array_has_adjacent_equal_goal.v
compiled=array_has_adjacent_equal_proof_auto.v
compiled=array_has_adjacent_equal_proof_manual.v
compiled=array_has_adjacent_equal_goal_check.v
compile_status=0
```

A final `find output/verify_20260422_045045_array_has_adjacent_equal/coq -type f ! -name '*.v' -print` produced no output.
