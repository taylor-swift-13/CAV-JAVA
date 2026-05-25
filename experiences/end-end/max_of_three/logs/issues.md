# Issues

## 2026-04-22T19:13:00+08:00 - Fingerprint controlled vocabulary

- Phenomenon: the initialized workspace fingerprint had an empty `semantic_description` and empty `keywords`.
- Trigger: beginning the Verify workflow for `input/max_of_three.c` in workspace `output/verify_20260422_191241_max_of_three`.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read repository-level `doc/retrieval/INDEX.md`, then filled `semantic_description` with the scalar max-of-three behavior and used only controlled keywords:
  - `algorithm_family: selection`
  - `control_flow: [straight_line, if]`
  - `data_shape: scalar_only`
  - `semantic_intent: return_max`
  - `proof_pattern: [pure_arithmetic, case_split]`
  - `edge_case_behavior: branch_on_order`
- Result: the fingerprint is non-empty and suitable for later retrieval.

## 2026-04-22T19:13:00+08:00 - No annotation changes needed

- Phenomenon: the active annotated C file was identical to the input C file, and the target function has no loop, heap predicate, pointer ownership, or array/string shape state requiring an `Inv` or intermediate `Assert`.
- Trigger: inspected `input/max_of_three.c` and `annotated/verify_20260422_191241_max_of_three.c`.
- Key C snippet:

```c
int m = a;

if (b > m) {
    m = b;
}
if (c > m) {
    m = c;
}

return m;
```

- Reasoning: the return proof is a pure branch case split over whether `b` replaces `a` and whether `c` replaces the current maximum. No persistent loop invariant or heap framing information is needed.
- Fix action: left the active annotated C file unchanged and intentionally did not create `logs/annotation_reasoning.md`.
- Result: symbolic execution could proceed directly from the unmodified active annotated file.

## 2026-04-22T19:13:42+08:00 - Symbolic execution with workspace logic path

- Phenomenon: the workspace initially had no generated VC files under `coq/generated/`.
- Trigger: first formal `symexec` run for the current active annotated C file.
- Command shape used:

```text
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=.../coq/generated/max_of_three_goal.v \
  --proof-auto-file=.../coq/generated/max_of_three_proof_auto.v \
  --proof-manual-file=.../coq/generated/max_of_three_proof_manual.v \
  --goal-check-file=.../coq/generated/max_of_three_goal_check.v \
  --input-file=annotated/verify_20260422_191241_max_of_three.c \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_191241_max_of_three \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function max_of_three
Successfully finished symbolic execution
```

The run generated `max_of_three_goal.v`, `max_of_three_proof_auto.v`, `max_of_three_proof_manual.v`, and `max_of_three_goal_check.v`.

## 2026-04-22T19:14:00+08:00 - Generated auto proof contains admitted lemmas, manual proof is empty

- Phenomenon: `coq/generated/max_of_three_proof_manual.v` contains only imports and no theorem obligations, while `coq/generated/max_of_three_proof_auto.v` contains four generated return lemmas with `Proof. Admitted.`:

```coq
Lemma proof_of_max_of_three_return_wit_1 : max_of_three_return_wit_1.
Proof. Admitted.
```

and similarly for `return_wit_2`, `return_wit_3`, and `return_wit_4`.

- Trigger: inspected generated Coq files after successful symbolic execution.
- Location: `coq/generated/max_of_three_goal.v` defines the four return witnesses; each is a pure arithmetic/case-split entailment selecting one branch of the postcondition disjunction.
- Fix action: did not duplicate these lemma names in `proof_manual.v`, because `goal_check.v` includes `max_of_three_proof_auto` before `max_of_three_proof_manual`, and defining the same `proof_of_*` names manually would collide. This matches the existing scalar `min_of_three` verification shape in the repository archive.
- Result: no manual proof edit was needed. `max_of_three_proof_manual.v` contains no `Admitted.`, no `admit`, and no added `Axiom`.

## 2026-04-22T19:14:41+08:00 - Full Coq compile replay and cleanup

- Phenomenon: verification is not complete after symbolic execution; `goal`, `proof_auto`, `proof_manual`, and `goal_check` must all compile under the documented workspace load path.
- Trigger: ran the full compile replay from `QualifiedCProgramming/SeparationLogic` using:
  - `-Q "$ORIG" ""`
  - `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_191241_max_of_three"`
  - the standard `SeparationLogic`, `unifysl`, `sets`, `compcert_lib`, `auxlibs`, `examples`, `StrategyLib`, `Common`, `fixedpoints`, `MonadLib`, and `listlib` roots.
- Result: `logs/compile_full.log` records:

```text
compiled=max_of_three_goal.v:success
compiled=max_of_three_proof_auto.v:success
compiled=max_of_three_proof_manual.v:success
compiled=max_of_three_goal_check.v:success
```

- Cleanup action: deleted all non-`.v` files under `coq/`. There is no workspace-local `input/` directory containing non-`.c`/non-`.v` intermediates to clean.
- Final result: `goal_check.v` compiles successfully, the manual proof file is clean, and only generated `.v` files remain under the workspace `coq/` directory.
