# Verification Issues

## 2026-04-22 01:39 CST - No annotation issue for straight-line scalar code

- Phenomenon: the active annotated C file `annotated/verify_20260422_013742_add_two.c` matched the input contract and implementation exactly:

```c
int add_two(int a, int b)
/*@ Require
      INT_MIN <= a + b &&
      a + b <= INT_MAX && emp
    Ensure
      __return == a@pre + b@pre && emp
*/
{
    return a + b;
}
```

- Trigger: this target has no loop, branch, pointer argument, heap predicate, or intermediate program point that would require a Verify-phase `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion.
- Localization: the only statement in the function body is `return a + b;`.
- Fix action: no annotation edit was made; `logs/annotation_reasoning.md` was intentionally skipped according to the verify workflow rule for tasks that need no additional Verify annotations.
- Result: symbolic execution proceeded directly on the current annotated file.

## 2026-04-22 01:39 CST - Workspace fingerprint placeholder filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords` object:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires the fingerprint to be filled early, after reading `doc/retrieval/INDEX.md`, using only the controlled keyword vocabulary defined there.
- Localization: `output/verify_20260422_013742_add_two/logs/workspace_fingerprint.json`.
- Fix action: populated `semantic_description` with the straight-line scalar addition semantics and used controlled keywords such as `straight_line`, `scalar_only`, `pure_arithmetic`, `overflow_guard`, and `int_range`; after final compile success, added controlled `verification_status: goal_check_passed`.
- Result: the fingerprint no longer contains the script-initialized empty placeholders.

## 2026-04-22 01:39 CST - Symbolic execution succeeded without generated manual obligations

- Phenomenon: a clean `symexec` run was required because this workspace initially had no generated Coq files under `coq/generated/`.
- Trigger: the verify workflow requires `symexec` to generate `goal`, `proof_auto`, `proof_manual`, and `goal_check` from the active annotated C file.
- Localization: `output/verify_20260422_013742_add_two/logs/qcp_run.log`.
- Fix action: created `coq/generated/`, cleared any stale generated files, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_013742_add_two.c \
  --goal-file=output/verify_20260422_013742_add_two/coq/generated/add_two_goal.v \
  --proof-auto-file=output/verify_20260422_013742_add_two/coq/generated/add_two_proof_auto.v \
  --proof-manual-file=output/verify_20260422_013742_add_two/coq/generated/add_two_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_013742_add_two \
  --no-exec-info
```

- Result: `qcp_run.log` ended with:

```text
End of symbolic execution of function add_two
Successfully finished symbolic execution
symexec_status=0
```

The generated files are `add_two_goal.v`, `add_two_proof_auto.v`, `add_two_proof_manual.v`, and `add_two_goal_check.v`.

## 2026-04-22 01:39 CST - Manual proof phase was unnecessary

- Phenomenon: `coq/generated/add_two_proof_manual.v` contained only imports and scope setup, with no theorem, lemma, proof body, `Admitted.`, or local `Axiom`.
- Trigger: the generated obligations for this straight-line addition are handled by the automatic proof module; the manual file has no remaining witness theorem to repair.
- Localization: `output/verify_20260422_013742_add_two/coq/generated/add_two_proof_manual.v`.
- Fix action: no manual proof edit was made, and `logs/proof_reasoning.md` was intentionally skipped according to the verify workflow rule for tasks with no manual proof target.
- Result: `rg -n "Admitted\.|\bAxiom\b|Theorem|Lemma|Proof\." add_two_proof_manual.v` found no matches.

## 2026-04-22 01:39 CST - Full Coq compile replay succeeded and intermediate artifacts were cleaned

- Phenomenon: completion requires compiling `goal`, `proof_auto`, `proof_manual`, and `goal_check`, not just generating them.
- Trigger: `goal_check.v` imports `add_two_goal`, `add_two_proof_auto`, and `add_two_proof_manual` under the workspace logical path `SimpleC.EE.CAV.verify_20260422_013742_add_two`.
- Localization: compile log `output/verify_20260422_013742_add_two/logs/compile.log`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled the generated files with the documented base `_CoqProject` load paths plus:

```bash
-Q "$ORIG" ""
-R "$GEN" "SimpleC.EE.CAV.verify_20260422_013742_add_two"
```

- Result: `compile.log` records:

```text
compiled=add_two_goal.v
compiled=add_two_proof_auto.v
compiled=add_two_proof_manual.v
compiled=add_two_goal_check.v
```

After compilation, all non-`.v` files under `coq/` were deleted. A final `find coq -type f ! -name '*.v'` produced no output.
