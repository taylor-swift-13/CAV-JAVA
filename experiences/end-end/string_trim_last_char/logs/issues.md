# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and an empty `keywords` object.
- Trigger: the verify workspace was initialized before task-specific semantic classification was filled in.
- Localization: `output/verify_20260423_045417_string_trim_last_char/logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md`, then filled in a non-empty semantic description and controlled-vocabulary keywords for a straight-line string/pointer in-place update with an `if` branch.
- Result: the fingerprint now records the task semantics and final `verification_status: goal_check_passed`.

## No annotation needed

- Phenomenon: the active annotated C had no additional `Inv` or `Assert` beyond the input contract.
- Trigger: the target function has no loop and no intermediate symbolic state that must be preserved across control-flow joins:

```c
{
    if (n > 0) {
        s[n - 1] = 0;
    }
}
```

- Localization: `annotated/verify_20260423_045417_string_trim_last_char.c`
- Fix: left the annotated C unchanged; the verifier can split the `if` branch and expose the two return witnesses directly.
- Result: `symexec` succeeded without annotation edits.

## Symexec invocation

- Phenomenon: the workspace did not yet contain generated Coq artifacts.
- Trigger: verification had to be generated from the active annotated C in this workspace.
- Command shape:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=.../coq/generated/string_trim_last_char_goal.v \
  --proof-auto-file=.../coq/generated/string_trim_last_char_proof_auto.v \
  --proof-manual-file=.../coq/generated/string_trim_last_char_proof_manual.v \
  --goal-check-file=.../coq/generated/string_trim_last_char_goal_check.v \
  --input-file=annotated/verify_20260423_045417_string_trim_last_char.c \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_045417_string_trim_last_char \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Localization: `logs/qcp_run.log`
- Fix: created `coq/generated/`, cleared any stale generated filenames, and ran the local `symexec` command above.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and `symexec_status: 0`; generated files are `string_trim_last_char_goal.v`, `string_trim_last_char_proof_auto.v`, `string_trim_last_char_proof_manual.v`, and `string_trim_last_char_goal_check.v`.

## Manual return witnesses

- Phenomenon: `string_trim_last_char_proof_manual.v` contained two admitted return witnesses:

```coq
Lemma proof_of_string_trim_last_char_return_wit_1 : string_trim_last_char_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_trim_last_char_return_wit_2 : string_trim_last_char_return_wit_2.
Proof. Admitted.
```

- Trigger: the generated postcondition is an assertion-level disjunction with an existential heap-list witness. The zero-length branch needs `lr = l ++ 0 :: nil`; the positive branch needs `lr = replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)`.
- Localization: `output/verify_20260423_045417_string_trim_last_char/coq/generated/string_trim_last_char_proof_manual.v`
- Fix: added local helper lemmas for `replace_Znth` length preservation and `Znth` at same/different indices, then proved the zero branch with `Left; Exists (l ++ 0 :: nil)` and the positive branch with `Right; Exists (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil))`.
- Result: `proof_manual.v` now has no `Admitted.` and no locally introduced `Axiom`.

## First manual compile failure

- Phenomenon: the first full compile replay failed in `proof_manual.v`:

```text
File ".../string_trim_last_char_proof_manual.v", line 104, characters 4-54:
Error: Found no subterm matching
"Zlength (replace_Znth ?M6125 ?M6126 ?M6127)" in the current goal.
```

- Trigger: after `entailer!`, the generated pure obligations were ordered as final-terminator read, replaced last-character read, prefix preservation, and length. The initial script assumed the length obligation came first.
- Localization: `logs/proof_reasoning.md` records the `coqtop` `Show` output for `string_trim_last_char_return_wit_2`.
- Fix: reordered the bullets so the first subgoal proves `Znth n_pre ... = 0` using `Znth_replace_Znth_diff`, `app_Znth2`, and `Znth0_cons`; the length lemma is now applied to the fourth subgoal.
- Result: the next full compile replay passed through `goal_check.v`.

## Compile replay and cleanup

- Phenomenon: final completion required compiling every generated Coq file under the workspace-specific logical path and then removing generated binary artifacts.
- Trigger: the verify completion rule requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, with no non-`.v` intermediates left under the workspace `coq/` tree.
- Localization: `logs/compile.log`
- Fix: compiled from `QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_045417_string_trim_last_char`; then deleted non-`.v` files under `coq/`.
- Result: `compile_status: 0`; only the four `.v` generated files remain under `coq/generated/`.
