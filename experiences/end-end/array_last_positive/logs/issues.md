# Issues: array_last_positive

## Fingerprint placeholder filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` for `keywords`.
- Trigger: the verify workspace had been initialized but no prior step had completed the required retrieval fingerprint update.
- Localization: `output/verify_20260422_053910_array_last_positive/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a semantic description for the left-to-right last-positive array scan. Keywords were selected only from the controlled vocabulary: `algorithm_family=search`, `control_flow=[for_loop, if]`, `data_shape=[array, pointer]`, `semantic_intent=preserve_input`, `proof_pattern=[loop_invariant, case_split, range_bound, heap_reasoning]`, `numeric_properties=[nonnegative_input, int_range]`, `edge_case_behavior=empty_loop_possible`, and after successful verification `verification_status=goal_check_passed`.
- Result: the fingerprint is no longer a placeholder and can be used by later retrieval.

## Missing loop invariant for last-positive prefix summary

- Phenomenon: the active annotated C initially had no `Inv` or loop-exit assertion:

```c
int i;
int ans = -1;

for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        ans = i;
    }
}

return ans;
```

- Trigger: the postcondition requires a global statement over the full array: either no element is positive, or `ans` is positive and every later index is nonpositive. Without a loop invariant, symbolic execution has no fact summarizing the already scanned prefix.
- Localization: `annotated/verify_20260422_053910_array_last_positive.c`, around the only `for (i = 0; i < n; ++i)` loop.
- Fix action: added a guarded-implication invariant that describes the processed prefix `[0, i)`, plus an exit assertion that specializes the same facts to `[0, n)` after proving `i == n`:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      -1 <= ans && ans < i &&
      Zlength(l) == n &&
      (ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] <= 0)) &&
      (0 <= ans => (l[ans] > 0 &&
                    (forall (j: Z), (ans < j && j < i) => l[j] <= 0))) &&
      IntArray::full(a, n, l)
*/
```

- Result: the invariant covers initialization, both loop branches, and the return postcondition. The guarded shape also avoids a top-level disjunction at the loop boundary.

## Symbolic execution had to be rerun after annotation changes

- Phenomenon: after adding `Inv` and `Assert`, the workflow required regenerating all Coq VC files from the latest annotated C.
- Trigger: the verify workflow treats any annotation change as changing the VC shape; stale `coq/generated/*` files must not be reused.
- Fix action: cleared stale generated targets and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_053910_array_last_positive.c \
  --goal-file=output/verify_20260422_053910_array_last_positive/coq/generated/array_last_positive_goal.v \
  --proof-auto-file=output/verify_20260422_053910_array_last_positive/coq/generated/array_last_positive_proof_auto.v \
  --proof-manual-file=output/verify_20260422_053910_array_last_positive/coq/generated/array_last_positive_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_053910_array_last_positive \
  --no-exec-info
```

- Relevant log excerpt from `logs/qcp_run.log`:

```text
Start to symbolic execution on program : annotated/verify_20260422_053910_array_last_positive.c
Symbolic Execution into function array_last_positive
End of symbolic execution of function array_last_positive
Successfully finished symbolic execution
symexec_status=0
```

- Result: fresh `array_last_positive_goal.v`, `array_last_positive_proof_auto.v`, `array_last_positive_proof_manual.v`, and `array_last_positive_goal_check.v` were generated.

## Manual proof obligations remained after symbolic execution

- Phenomenon: `coq/generated/array_last_positive_proof_manual.v` contained four admitted manual lemmas:

```coq
proof_of_array_last_positive_entail_wit_1
proof_of_array_last_positive_entail_wit_2_1
proof_of_array_last_positive_entail_wit_3
proof_of_array_last_positive_return_wit_1
```

- Trigger: the loop invariant generated pure entailment witnesses for initialization, the positive branch, loop exit, and final assertion-level disjunction.
- Localization: `output/verify_20260422_053910_array_last_positive/coq/generated/array_last_positive_proof_manual.v`.
- Fix action: replaced all four `Admitted.` placeholders with completed proofs. The first two are solved by `unfold; intros; entailer!`. `entail_wit_3` derives `i = n_pre` from the exit bounds and applies the saved guarded implication hypotheses. `return_wit_1` uses `pre_process`, splits on `Z.eq_dec ans (-1)`, and chooses assertion-level `Right` for the no-positive case or `Left` for the positive-index case.
- Representative final return proof:

```coq
Lemma proof_of_array_last_positive_return_wit_1 : array_last_positive_return_wit_1.
Proof.
  unfold array_last_positive_return_wit_1.
  pre_process.
  destruct (Z.eq_dec ans (-1)) as [Hans_eq | Hans_neq].
  - Right.
    entailer!.
  - assert (Hans_nonneg : 0 <= ans) by lia.
    destruct (H4 Hans_nonneg) as [Hans_val Hlast].
    Left.
    entailer!.
Qed.
```

- Result: `array_last_positive_proof_manual.v` has no `Admitted.` proof bodies and no new local `Axiom`.

## Full Coq compile and cleanup

- Phenomenon: successful symbolic execution is not enough for Verify success; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must all compile with the workspace load path, and Coq build products must be removed afterward.
- Trigger condition: normal final verification after manual proof edits.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` using the documented base `-R` flags plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_053910_array_last_positive`.
- Relevant compile log from `logs/compile.log`:

```text
compile array_last_positive_goal.v
compile array_last_positive_proof_auto.v
compile array_last_positive_proof_manual.v
compile array_last_positive_goal_check.v
compile_status=0
```

- Result: all four Coq files compiled successfully. Non-`.v` files under `coq/` were deleted, leaving only `array_last_positive_goal.v`, `array_last_positive_proof_auto.v`, `array_last_positive_proof_manual.v`, and `array_last_positive_goal_check.v`.
