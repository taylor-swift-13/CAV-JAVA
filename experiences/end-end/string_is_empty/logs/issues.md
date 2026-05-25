# Verification Issues

## Fingerprint placeholders completed early

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty semantic description and empty keyword set:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the workspace was initialized before task-specific semantic classification, but the verify workflow requires these fields to be filled early using only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260423_030819_string_is_empty/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the description for a straight-line string sentinel check and used only controlled values such as `selection`, `if`, `string`, `pointer`, `preserve_input`, `case_split`, and `heap_reasoning`. After successful verification, added controlled `verification_status` values.
- Result: the fingerprint is non-empty and uses only the controlled vocabulary.

## Symexec generated two manual return witnesses

- Phenomenon: `symexec` succeeded on the active annotated C without needing additional `Inv` or `Assert`, but generated two manual proof obligations.
- Trigger: the implementation branches on `s[0]`; the postcondition is a disjunction over `n == 0` and `0 < n`, so the return witnesses need pure reasoning connecting the first character of `l ++ [0]` to the string length.
- Localization: active annotated file `annotated/verify_20260423_030819_string_is_empty.c`; generated file `output/verify_20260423_030819_string_is_empty/coq/generated/string_is_empty_proof_manual.v`.
- Key generated obligations:

```coq
Lemma proof_of_string_is_empty_return_wit_1 : string_is_empty_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_is_empty_return_wit_2 : string_is_empty_return_wit_2.
Proof. Admitted.
```

- Symexec log evidence:

```text
Symbolic Execution into function string_is_empty
End of symbolic execution of function string_is_empty
Successfully finished symbolic execution
symexec_status=0
```

- Fix action: kept the annotated C unchanged and proved the two return witnesses manually.
- Result: `symexec` generated fresh `string_is_empty_goal.v`, `string_is_empty_proof_auto.v`, `string_is_empty_proof_manual.v`, and `string_is_empty_goal_check.v`.

## Manual proof needed list append index lemmas

- Phenomenon: the generated manual proof file imported `List_lemma` but the concise proof needed `app_Znth1` and `app_Znth2`.
- Trigger: both return witnesses reason about `Znth 0 (l ++ 0 :: nil) 0`. In the zero branch, assuming `0 < n` lets `app_Znth1` rewrite the read into the nonzero prefix and contradict the contract. In the nonzero branch, assuming `n = 0` lets `app_Znth2` rewrite the read into the terminator and contradict `s[0] != 0`.
- Localization: `output/verify_20260423_030819_string_is_empty/coq/generated/string_is_empty_proof_manual.v`.
- Fix action: added `ListLib` to the AUXLib import line:

```coq
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap ListLib.
```

Then replaced both admitted bodies with proofs using `pre_process`, pure assertions for `n = 0` or `0 < n`, assertion-level `Right` / `Left`, and `entailer!`.
- Result: `string_is_empty_proof_manual.v` compiles and `rg -n "Admitted\.|^\s*Axiom\b"` on the manual proof file returns no matches.

## Compile replay and cleanup

- Phenomenon: final verification requires more than successful `symexec`; all generated Coq files must compile under the workspace logical path and intermediate products must be removed.
- Trigger: the final correctness module in `string_is_empty_goal_check.v` includes both auto and manual proof modules:

```coq
From SimpleC.EE.CAV.verify_20260423_030819_string_is_empty
  Require Import string_is_empty_goal string_is_empty_proof_auto string_is_empty_proof_manual.
```

- Localization: compile logs under `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, and `logs/compile_goal_check.log`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_030819_string_is_empty`; then deleted all non-`.v` files under the workspace `coq/` tree. The repository `input/` directory had no non-`.c`/non-`.v` intermediates.
- Result: all four compile logs are empty, `goal_check.v` compiled successfully, and `find output/verify_20260423_030819_string_is_empty/coq -type f ! -name '*.v'` returns no files.
