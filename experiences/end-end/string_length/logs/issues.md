# Verification Issues

## Documentation path was not present inside workspace

- Symptom: the task requested reading `doc/retrieval/INDEX.md` early, but from workspace `output/verify_20260423_121011_string_length` the relative path did not exist.
- Triggering command:

```text
sed -n '1,240p' doc/retrieval/INDEX.md
sed: can't read doc/retrieval/INDEX.md: No such file or directory
```

- Diagnosis: this workspace contains only `coq/`, `logs/`, and `original/`; the shared workflow documentation lives at repository path `doc/retrieval/INDEX.md`.
- Fix: read the repository documentation path and then updated `logs/workspace_fingerprint.json` with a non-empty semantic description and controlled-vocabulary keywords only.
- Result: fingerprint now describes the read-only null-terminated string scan and uses controlled keys such as `algorithm_family`, `control_flow`, `data_shape`, `semantic_intent`, `proof_pattern`, `numeric_properties`, and `edge_case_behavior`.

## Initial symexec invocation used the wrong strategy flag shape

- Symptom: the first manual `symexec` command failed before parsing the annotated C file completely.
- Triggering log from `logs/qcp_run.log`:

```text
symexec_start=2026-04-23T12:13:35+08:00
fatal error: Cannot Open DSLFileLists char_array.
symexec_end=2026-04-23T12:13:35+08:00
symexec_status=1
```

- Cause: I passed explicit repeated strategy options:

```text
--strategy-file=common
--strategy-file=char_array
```

The binary treated the second value as a DSL file list input instead of as an additional strategy include. A second attempt with `--strategy-file=common,char_array` similarly failed with `Cannot Open DSLFileLists common,char_array`.

- Fix: remove the explicit `--strategy-file` arguments and keep only `--strategy-folder-path=QualifiedCProgramming/QCP_examples/`. The annotated C includes `verification_stdlib.h` and `char_array_def.h`, whose annotations include `common.strategies` and `char_array.strategies`.
- Result: `symexec` parsed both strategy files via include annotations, entered `string_length`, generated all four Coq files, and ended with:

```text
End of symbolic execution of function string_length
Start to print Coq files for the program annotated/verify_20260423_121011_string_length.c
Successfully finished symbolic execution
symexec_status=0
```

## Manual string-scan branch witnesses were required

- Symptom: `coq/generated/string_length_proof_manual.v` contained two generated admitted lemmas:

```coq
Lemma proof_of_string_length_entail_wit_2 : string_length_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_length_entail_wit_3 : string_length_entail_wit_3.
Proof. Admitted.
```

- Relevant VC shape: `string_length_entail_wit_2` has the nonzero branch assumption `Znth i (l ++ 0 :: nil) 0 <> 0` and must prove the next loop invariant after `i++`, especially `(i + 1) <= n`. `string_length_entail_wit_3` has the zero branch assumption `Znth i (l ++ 0 :: nil) 0 = 0` and must prove the loop-exit assertion, including changing the local store from `i` to `n`.
- Fix: prove both by first deriving the key bound/equality:
  - In `entail_wit_2`, prove `i < n`; otherwise `i = n`, and `app_Znth2` plus `Zlength l = n` rewrites the branch assumption to `0 <> 0`.
  - In `entail_wit_3`, prove `i = n`; if `i < n`, `app_Znth1` rewrites the zero branch to `Znth i l 0 = 0`, contradicting the contract fact that all payload indices are nonzero.
- Result: `coq/generated/string_length_proof_manual.v` now proves both lemmas with `pre_process`, explicit `Z_lt_ge_dec` splits, `app_Znth1` / `app_Znth2`, and `entailer!`. A search for manual bypasses reports no `Admitted.` or newly added `Axiom` in `proof_manual.v`; the only match is the existing import line `From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.`

## Final compile and cleanup

- Compile command location: `QualifiedCProgramming/SeparationLogic`.
- Compiled files in order:
  - `coq/generated/string_length_goal.v`
  - `coq/generated/string_length_proof_auto.v`
  - `coq/generated/string_length_proof_manual.v`
  - `coq/generated/string_length_goal_check.v`
- Result from `logs/coq_compile.log`:

```text
compile_end=2026-04-23T12:15:20+08:00
compile_status=0
```

- Cleanup: removed non-`.v` Coq intermediates under the workspace `coq/` directory. The remaining Coq files are exactly:

```text
coq/generated/string_length_goal.v
coq/generated/string_length_goal_check.v
coq/generated/string_length_proof_auto.v
coq/generated/string_length_proof_manual.v
```

- Experience update decision: no repository-level experience file was edited because the task explicitly constrained work to the existing workspace. The reusable strategy-invocation detail is recorded here for handoff.
