# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace had been bootstrapped but not yet semantically classified.
- Localization: `output/verify_20260422_223908_string_all_lowercase/logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md` and filled in a description of the null-terminated string scan. The controlled keywords classify the function as a string/pointer search with `while_loop`, `if`, `loop_invariant`, `case_split`, `heap_reasoning`, `range_bound`, and `empty_loop_possible`; after final verification the fingerprint also records `verification_status: goal_check_passed`.
- Result: the fingerprint no longer contains empty placeholders and uses only the controlled vocabulary.

## Annotation Layer

- Phenomenon: the active annotated file initially had no invariant for the `while (1)` scan loop:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] < 97 || s[i] > 122) {
        return 0;
    }
    i++;
}
```

- Trigger: the postcondition requires `__return == string_all_lowercase_spec(l)`, but the loop needs to remember that all characters in the processed prefix are lowercase and that the original `CharArray::full` resource is preserved.
- Localization: `annotated/verify_20260422_223908_string_all_lowercase.c`
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md` and added this loop-head invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_all_lowercase_spec(l1) == 1 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Result: the invariant supplies initialization (`l1 = nil`, `l2 = l`), loop preservation after consuming a lowercase character, early-return semantics for out-of-range characters, and exit semantics at the terminating zero.

## Symexec Invocation

- Phenomenon: after annotation changes, fresh VC generation was required.
- Trigger: `INV.md`/`SYMEXEC.md` require rerunning `symexec` whenever an invariant changes and clearing stale generated files first.
- Localization: `logs/qcp_run.log`
- Fix: created `coq/generated/`, removed stale generated targets, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file="$GEN/string_all_lowercase_goal.v" \
  --proof-auto-file="$GEN/string_all_lowercase_proof_auto.v" \
  --proof-manual-file="$GEN/string_all_lowercase_proof_manual.v" \
  --proof-check-file="$GEN/string_all_lowercase_goal_check.v" \
  --input-file=annotated/verify_20260422_223908_string_all_lowercase.c \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_223908_string_all_lowercase \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ends with:

```text
Symbolic Execution into function string_all_lowercase
End of symbolic execution of function string_all_lowercase
Successfully finished symbolic execution
symexec_status=0
```

Fresh `string_all_lowercase_goal.v`, `string_all_lowercase_proof_auto.v`, `string_all_lowercase_proof_manual.v`, and `string_all_lowercase_goal_check.v` were generated.

## Manual Proof

- Phenomenon: `coq/generated/string_all_lowercase_proof_manual.v` contained five generated `Admitted.` placeholders:

```coq
proof_of_string_all_lowercase_entail_wit_1
proof_of_string_all_lowercase_entail_wit_2
proof_of_string_all_lowercase_return_wit_1
proof_of_string_all_lowercase_return_wit_2
proof_of_string_all_lowercase_return_wit_3
```

- Trigger: `symexec` generated pure list/spec obligations for initializing and preserving the prefix invariant, plus return witnesses for high out-of-range, low out-of-range, and terminator branches.
- Localization: `output/verify_20260422_223908_string_all_lowercase/coq/generated/string_all_lowercase_proof_manual.v`
- Fix: adapted the verified `examples/string_all_digits` proof shape to the lowercase range by adding:

```coq
string_all_lowercase_spec_app_lower
string_all_lowercase_spec_app_bad_high
string_all_lowercase_spec_app_bad_low
```

Then replaced all five generated proof bodies. The key proof split is:

- `entail_wit_1`: choose `l1 = nil`, `l2 = l`.
- `entail_wit_2`: use `CharArray.full_length`, prove `i < n`, destruct `l2_2`, append the current lowercase head to `l1_2`, and apply `string_all_lowercase_spec_app_lower`.
- `return_wit_1`: destruct the suffix head and apply `string_all_lowercase_spec_app_bad_high` for `x > 122`.
- `return_wit_2`: destruct the suffix head and apply `string_all_lowercase_spec_app_bad_low` for `x < 97`.
- `return_wit_3`: use the no-interior-zero premise to prove `i = n`; then the remaining suffix must be empty and the processed prefix is the full list.

- Result: `rg -n "Admitted\\.|^Axiom\\b" coq/generated/string_all_lowercase_proof_manual.v` returns no matches.

## Compile Replay

- Phenomenon: final verification requires compiling the generated Coq chain under the current workspace load path.
- Trigger: the completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile.
- Localization: `logs/compile.log`
- Fix: compiled from `QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_223908_string_all_lowercase`.
- Result: `logs/compile.log` records:

```text
compiled=original/string_all_lowercase.v
compiled=generated/string_all_lowercase_goal.v
compiled=generated/string_all_lowercase_proof_auto.v
compiled=generated/string_all_lowercase_proof_manual.v
compiled=generated/string_all_lowercase_goal_check.v
compile_status=0
```

## Cleanup

- Phenomenon: `coqc` produced normal `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` build outputs.
- Trigger: compilation of the original spec and generated Coq files.
- Localization: `output/verify_20260422_223908_string_all_lowercase/coq/`, `output/verify_20260422_223908_string_all_lowercase/original/`, and `input/`.
- Fix: deleted non-`.v` files under the workspace `coq/`, deleted non-source Coq build outputs under `original/`, and checked `input/` for non-`.c`/`.v` intermediates.
- Result: `find output/verify_20260422_223908_string_all_lowercase/coq input -type f \( ! -name '*.v' ! -name '*.c' \) -print` returns no files.
