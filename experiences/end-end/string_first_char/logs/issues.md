# Verification Issues

## Fingerprint initialized from retrieval vocabulary

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` for `keywords`, which violates the verify workflow requirement for retrieval-ready workspaces.
- Trigger: early workspace inspection before symbolic execution.
- Localization: `output/verify_20260423_025022_string_first_char/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a concrete semantic description for the straight-line `string_first_char` function. The selected keyword keys and values use only the controlled vocabulary:

```json
"algorithm_family": "selection",
"control_flow": "straight_line",
"data_shape": ["string", "pointer"],
"semantic_intent": "preserve_input",
"proof_pattern": ["heap_reasoning", "pure_arithmetic"],
"numeric_properties": "int_range"
```

- Result: the fingerprint is non-empty and, after final verification, records controlled verification status values including `manual_witness_needed`, `goal_check_passed`, and `proof_check_passed`.

## Initial `symexec` invocation used `--input-file` incorrectly

- Phenomenon: the first manual `symexec` command exited before parsing the annotated C file. The log showed:

```text
symexec_start=2026-04-23T02:51:08+08:00
cannot open file output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_goal_check.v
fopen error: No such file or directory
```

- Trigger: I passed the future `goal_check.v` output path with `--input-file=...`, which this binary treats as the existing C input path.
- Localization: `logs/qcp_run.log` during the first attempt. The final `qcp_run.log` was overwritten by the successful rerun, so the exact failed text is preserved here.
- Fix action: reran `symexec` with the canonical equals-form options:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260423_025022_string_first_char.c \
  --goal-file=output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_goal.v \
  --proof-auto-file=output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_proof_auto.v \
  --proof-manual-file=output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_proof_manual.v \
  --goal-check-file=output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_goal_check.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_025022_string_first_char \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Result: `symexec` exited with status `0`, parsed `common.strategies` and `char_array.strategies`, and generated fresh `string_first_char_goal.v`, `string_first_char_proof_auto.v`, `string_first_char_proof_manual.v`, and `string_first_char_goal_check.v`.

## Manual return witness required the local `app_Znth1` lemma

- Phenomenon: fresh `string_first_char_proof_manual.v` contained one generated manual stub:

```coq
Lemma proof_of_string_first_char_return_wit_1 : string_first_char_return_wit_1.
Proof. Admitted.
```

- Trigger: the return VC needed the pure bridge:

```coq
Znth 0 (app l (cons 0 nil)) 0 = Znth 0 l 0
```

under `1 <= n` and `Zlength l = n`, while preserving the identical `CharArray.full` spatial resource.
- Localization: `output/verify_20260423_025022_string_first_char/coq/generated/string_first_char_proof_manual.v`.
- Fix action: replaced the generated `Admitted` with:

```coq
Proof.
  pre_process.
  entailer!.
  rewrite app_Znth1; lia.
Qed.
```

- Result: `string_first_char_proof_manual.v` compiles, contains no `Admitted.`, no `admit.`, and no top-level `Axiom`.

## First proof compile used the wrong list lemma name

- Phenomenon: the first compile replay failed after compiling `goal.v` and `proof_auto.v`:

```text
File ".../string_first_char_proof_manual.v", line 25, characters 10-19:
Error: The variable Znth_app1 was not found in the current environment.
```

- Trigger: I initially wrote `rewrite Znth_app1; lia.`, but the imported project lemma is named `app_Znth1`.
- Localization: `logs/compile.log`, `string_first_char_proof_manual.v:25`.
- Fix action: changed the proof line to `rewrite app_Znth1; lia.`.
- Result: the next full replay compiled `string_first_char_goal.v`, `string_first_char_proof_auto.v`, `string_first_char_proof_manual.v`, and `string_first_char_goal_check.v` successfully.

## Final compile and cleanup

- Phenomenon: verify completion requires more than successful `symexec`; the full Coq replay must pass and generated build intermediates must be removed.
- Trigger: normal finalization after proving the manual witness.
- Localization: `logs/compile.log` and `coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject` load paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_025022_string_first_char`. There is no task-specific `original/string_first_char.v`, so that optional compile step was skipped. Then removed all non-`.v` files under this workspace's `coq/` tree and checked the input directory for non-`.c`/non-`.v` byproducts.
- Result: `logs/compile.log` records successful compilation through `string_first_char_goal_check.v`; `find coq -type f ! -name '*.v'` is empty; the input byproduct check is empty.
