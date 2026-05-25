# Verify issues

## Fingerprint placeholder filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty semantic description and empty keywords:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and replacing placeholder values with a non-empty summary and controlled-vocabulary keywords.
- Location: `output/verify_20260423_024227_string_find_char/logs/workspace_fingerprint.json`.
- Fix action: filled the semantic description with the read-only null-terminated string search behavior: scan from index `0`, return the first index whose logical character equals `c`, or return `-1` after reaching the terminator. Used only controlled vocabulary values such as `algorithm_family: search`, `control_flow: while_loop`, `data_shape: [string, pointer]`, `semantic_intent: preserve_input`, and proof patterns including `loop_invariant`, `case_split`, `termination_by_bound`, `range_bound`, and `heap_reasoning`.
- Result: after successful verification, the fingerprint also records `verification_status: [goal_check_passed, proof_check_passed]`.

## Missing scan invariant and loop-exit assertion

- Phenomenon: the active annotated file initially matched the input file and had no `Inv` before the `while (1)` scan loop. Without an invariant, symbolic execution would not retain the processed-prefix fact needed by both return paths.
- Triggering C snippet:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        return i;
    }
    i++;
}

return -1;
```

- Location: `annotated/verify_20260423_024227_string_find_char.c`, around the only loop.
- Fix action: after recording the reasoning in `logs/annotation_reasoning.md`, added a loop invariant preserving the full string heap, unchanged `s` and `c`, the index range, the `n < INT_MAX` bound, the logical length, the original nonzero-prefix contract, and the key first-match history:

```c
/*@ Inv Assert
      0 <= i && i <= n &&
      n < INT_MAX &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Fix action: added a loop-exit assertion immediately before `return -1` to expose that the terminating zero implies `i == n`, so the processed-prefix no-match fact covers all of `l`:

```c
/*@ Assert
      i == n &&
      n < INT_MAX &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Result: the final `symexec` run succeeded on the current annotated file and generated fresh `string_find_char_goal.v`, `string_find_char_proof_auto.v`, `string_find_char_proof_manual.v`, and `string_find_char_goal_check.v`. The final `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function string_find_char
Successfully finished symbolic execution
symexec_status=0
```

## Increment safety VC showed the invariant had dropped `n < INT_MAX`

- Phenomenon: the first successful `symexec` generated a manual safety witness that could not prove the increment bound:

```coq
Definition string_find_char_safety_wit_4 :=
forall ... (n : Z) ... (i : Z),
  [| 0 <= i |] &&
  [| i <= n |] &&
  [| Zlength l = n |] &&
  ...
|--
  [| i + 1 <= INT_MAX |] && ...
```

- Trigger: the original contract had `n < INT_MAX`, but the first invariant did not preserve it. Since the loop increments `i`, the VC needed `i <= n` together with `n < INT_MAX`.
- Location: generated `coq/generated/string_find_char_goal.v`, witness `string_find_char_safety_wit_4`; source annotation in `annotated/verify_20260423_024227_string_find_char.c`.
- Fix action: added `n < INT_MAX` to both the invariant and the exit assertion, cleared generated Coq files, and reran `symexec`.
- Result: the revised generated manual file no longer contains `string_find_char_safety_wit_4`; the remaining manual obligations are semantic entailment/return witnesses.

## Manual proof of terminator and found-branch witnesses

- Phenomenon: after the final `symexec`, `coq/generated/string_find_char_proof_manual.v` contained three admitted obligations:

```coq
Lemma proof_of_string_find_char_entail_wit_2 : string_find_char_entail_wit_2.
Proof. Admitted.
Lemma proof_of_string_find_char_entail_wit_3 : string_find_char_entail_wit_3.
Proof. Admitted.
Lemma proof_of_string_find_char_return_wit_1 : string_find_char_return_wit_1.
Proof. Admitted.
```

- Localization: `entail_wit_2` is the loop preservation path after `s[i] != 0` and `s[i] != c`; `entail_wit_3` is the break path where `s[i] == 0`; `return_wit_1` is the branch where `s[i] == c`.
- Fix action: replaced the stubs with proofs that first derive the key index fact:
  - In preservation and found-branch witnesses, `Znth i (l ++ 0 :: nil) 0 <> 0` plus `i <= n` proves `i < n`; otherwise `i = n` would read the appended terminator `0`.
  - In the break witness, `Znth i (l ++ 0 :: nil) 0 = 0` and the precondition that all `l[0..n)` are nonzero prove `i = n`.
  - With those facts, `app_Znth1` or `app_Znth2` converts between the physical string list `l ++ [0]` and the logical list `l`, and `entailer!` closes the separation goals.
- Result: `coq/generated/string_find_char_proof_manual.v` contains no `Admitted.` and no newly added `Axiom`. The complete compile replay succeeded through `string_find_char_goal_check.v`.

## Full compile replay and cleanup

- Phenomenon: successful `symexec` is not enough for final Verify success; the workflow requires compiling all generated Coq files and then deleting non-`.v` intermediates.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the documented base load paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_024227_string_find_char`. There is no `original/string_find_char.v`, so the optional original compile was skipped.
- Result: `logs/compile.log` records:

```text
compiled string_find_char_goal.v
compiled string_find_char_proof_auto.v
compiled string_find_char_proof_manual.v
compiled string_find_char_goal_check.v
compile_status=0
```

- Cleanup result: `find coq -type f ! -name '*.v' -print` produced no output after cleanup. `find ./input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v' -print` also produced no output.
