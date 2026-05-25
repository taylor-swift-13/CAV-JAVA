# Verification Issues

## 2026-04-22 05:35 +0800 - Fingerprint initialized before verification

- Phenomenon: the workspace was initialized with an empty retrieval fingerprint:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires `logs/workspace_fingerprint.json` to be populated early, after reading `doc/retrieval/INDEX.md`, with a non-empty semantic description and keywords drawn only from the controlled vocabulary.
- Localization: `output/verify_20260422_053439_array_last/logs/workspace_fingerprint.json`.
- Fix action: filled the semantic description for a straight-line read-only integer-array function that returns the last element and preserves `IntArray::full(a, n, l)`. Used only controlled keyword keys and values: `algorithm_family: selection`, `control_flow: straight_line`, `data_shape: [array, pointer]`, `semantic_intent: preserve_input`, `proof_pattern: [pure_arithmetic, heap_reasoning]`, and `numeric_properties: [nonnegative_input, int_range]`.
- Result: the fingerprint is now usable for retrieval. After final verification it was extended with controlled `verification_status` values `goal_check_passed` and `proof_check_passed`.

## 2026-04-22 05:35 +0800 - No annotation repair was needed

- Phenomenon: the active annotated C copy already matched the input contract and contained no loop or branch requiring an `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion.
- Trigger: the function body is a single read and return:

```c
int array_last(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == l[n@pre - 1] &&
      IntArray::full(a, n@pre, l)
*/
{
    return a[n - 1];
}
```

- Localization: `annotated/verify_20260422_053439_array_last.c`.
- Fix action: left the annotated C unchanged and skipped `logs/annotation_reasoning.md` because there was no concrete annotation failure to analyze or repair.
- Result: symbolic execution could proceed directly from the active annotated file.

## 2026-04-22 05:35 +0800 - Symbolic execution generated fresh Coq files

- Phenomenon: the workspace initially had no generated Coq proof files under `coq/generated/`, so verification needed a fresh `symexec` run.
- Trigger: Verify success requires generated `goal`, `proof_auto`, `proof_manual`, and `goal_check` files based on the current active annotated C file.
- Localization: `logs/qcp_run.log`.
- Fix action: created `coq/generated/`, cleared stale generated targets if present, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_053439_array_last.c \
  --goal-file=output/verify_20260422_053439_array_last/coq/generated/array_last_goal.v \
  --proof-auto-file=output/verify_20260422_053439_array_last/coq/generated/array_last_proof_auto.v \
  --proof-manual-file=output/verify_20260422_053439_array_last/coq/generated/array_last_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_053439_array_last \
  --no-exec-info
```

- Result: `symexec` exited with status `0`. The key log ending was:

```text
End of symbolic execution of function array_last
Successfully finished symbolic execution
symexec_status=0
```

It generated `array_last_goal.v`, `array_last_proof_auto.v`, `array_last_proof_manual.v`, and `array_last_goal_check.v`.

## 2026-04-22 05:36 +0800 - No manual proof obligations remained

- Phenomenon: `coq/generated/array_last_proof_manual.v` contained only imports and scope openings, with no `Lemma`, `Theorem`, or `Admitted.` placeholder.
- Trigger: the straight-line array-read proof was completely discharged by the generated goal and automatic proof artifacts.
- Localization: `output/verify_20260422_053439_array_last/coq/generated/array_last_proof_manual.v`.
- Fix action: skipped `logs/proof_reasoning.md` and manual proof editing because there was no theorem or witness to prove. Confirmed with:

```bash
rg -n "Admitted\.|^\s*Axiom\b|Lemma|Theorem" coq/generated/array_last_proof_manual.v
```

- Result: the search returned no matches; `proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.

## 2026-04-22 05:36 +0800 - Full Coq compile replay and cleanup succeeded

- Phenomenon: successful `symexec` alone is not sufficient; the workflow requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting Coq intermediate files.
- Trigger: Coq compilation creates `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`, while final completion requires the workspace `coq/` tree to contain only `.v` files.
- Localization: `logs/compile.log` and `output/verify_20260422_053439_array_last/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_053439_array_last`; then deleted all non-`.v` files under the workspace `coq/` tree.
- Result: `logs/compile.log` records:

```text
compiled array_last_goal.v
compiled array_last_proof_auto.v
compiled array_last_proof_manual.v
compiled array_last_goal_check.v
compile_status=0
```

After cleanup, the remaining Coq files are exactly the four generated `.v` files.
