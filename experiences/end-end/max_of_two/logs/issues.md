# Issues

## 2026-04-22T19:19:56+08:00 - Fingerprint controlled vocabulary

- Phenomenon: the initialized workspace fingerprint had an empty `semantic_description` and empty `keywords`, which violates the Verify workflow requirement for early retrieval metadata.
- Trigger: beginning the Verify workflow for `input/max_of_two.c` in workspace `output/verify_20260422_191732_max_of_two`.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled `semantic_description` with the scalar max-of-two behavior and used only controlled keywords:
  - `algorithm_family: selection`
  - `control_flow: if`
  - `data_shape: scalar_only`
  - `semantic_intent: return_max`
  - `proof_pattern: [pure_arithmetic, case_split]`
  - `edge_case_behavior: branch_on_order`
- Result: the fingerprint is non-empty and uses only the retrieval index vocabulary.

## 2026-04-22T19:19:56+08:00 - No annotation changes needed

- Phenomenon: the active annotated C file was identical to the input C file, and the target function has no loop, heap predicate, pointer ownership, or array/string shape state requiring an `Inv` or intermediate `Assert`.
- Trigger: inspected `input/max_of_two.c` and `annotated/verify_20260422_191732_max_of_two.c`.
- Key C snippet:

```c
if (a >= b) {
    return a;
} else {
    return b;
}
```

- Reasoning: the postcondition is a pure arithmetic case split. In the `a >= b` branch, `__return == a@pre` and `b@pre <= __return`; in the `a < b` branch, `__return == b@pre` and `a@pre <= __return`.
- Fix action: left the active annotated C file unchanged and intentionally did not create `logs/annotation_reasoning.md`.
- Result: symbolic execution could proceed directly from the unmodified active annotated file.

## 2026-04-22T19:19:56+08:00 - Symbolic execution with workspace logic path

- Phenomenon: the workspace initially had no generated VC files under `coq/generated/`.
- Trigger: first formal `symexec` run for the current active annotated C file.
- Command shape used:

```text
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=.../coq/generated/max_of_two_goal.v \
  --proof-auto-file=.../coq/generated/max_of_two_proof_auto.v \
  --proof-manual-file=.../coq/generated/max_of_two_proof_manual.v \
  --goal-check-file=.../coq/generated/max_of_two_goal_check.v \
  --input-file=annotated/verify_20260422_191732_max_of_two.c \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_191732_max_of_two \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function max_of_two
Successfully finished symbolic execution
```

The run generated `max_of_two_goal.v`, `max_of_two_proof_auto.v`, `max_of_two_proof_manual.v`, and `max_of_two_goal_check.v`.

## 2026-04-22T19:19:56+08:00 - Generated auto proof contains admitted lemmas, manual proof is empty

- Phenomenon: `coq/generated/max_of_two_proof_manual.v` contains only imports and no theorem obligations, while `coq/generated/max_of_two_proof_auto.v` contains two generated return lemmas with `Proof. Admitted.`:

```coq
Lemma proof_of_max_of_two_return_wit_1 : max_of_two_return_wit_1.
Proof. Admitted.
Lemma proof_of_max_of_two_return_wit_2 : max_of_two_return_wit_2.
Proof. Admitted.
```

- Trigger: inspected generated Coq files after successful symbolic execution.
- Location: `coq/generated/max_of_two_goal.v` defines the two return witnesses; each is a pure arithmetic/case-split entailment for one branch of the postcondition disjunction.
- Fix action: did not duplicate these lemma names in `proof_manual.v`, because `goal_check.v` includes `max_of_two_proof_auto` before `max_of_two_proof_manual`, and defining the same `proof_of_*` names manually would collide. This matches the verified scalar `max_of_three` workflow in the local examples.
- Result: no manual proof edit was needed. `max_of_two_proof_manual.v` contains no `Admitted.`, no `admit`, and no added `Axiom`.

## 2026-04-22T19:19:56+08:00 - Full Coq compile replay and cleanup

- Phenomenon: verification is not complete after symbolic execution; `goal`, `proof_auto`, `proof_manual`, and `goal_check` must all compile under the documented workspace load path.
- Trigger: ran the full compile replay from `QualifiedCProgramming/SeparationLogic` using the documented `COMPILE.md` template with:
  - `-Q "$ORIG" ""`
  - `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_191732_max_of_two"`
  - the standard `SeparationLogic`, `unifysl`, `sets`, `compcert_lib`, `auxlibs`, `examples`, `StrategyLib`, `Common`, `fixedpoints`, `MonadLib`, and `listlib` roots.
- Result: `logs/compile_full.log` records:

```text
compiled=max_of_two_goal.v:success
compiled=max_of_two_proof_auto.v:success
compiled=max_of_two_proof_manual.v:success
compiled=max_of_two_goal_check.v:success
```

- Cleanup action: deleted all non-`.v` files under `coq/`. There is no workspace-local `input/` directory containing non-`.c`/non-`.v` intermediates to clean.
- Final result: `goal_check.v` compiles successfully, the manual proof file is clean, and only generated `.v` files remain under the workspace `coq/` directory.
