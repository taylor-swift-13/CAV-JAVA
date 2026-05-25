# Verification Issues

## Issue 1: fresh symbolic execution was required for the active annotated file

- Phenomenon: the workspace initially contained no generated Coq files under `coq/generated/`, so verification could not proceed to proof or `goal_check`.
- Trigger: the active annotated file was `annotated/verify_20260422_175633_is_multiple.c`, and the workflow requires generated VCs to match that exact file.
- Command used:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_175633_is_multiple.c \
  --goal-file=output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_goal.v \
  --proof-auto-file=output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_proof_auto.v \
  --proof-manual-file=output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_175633_is_multiple \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_end: 2026-04-22T17:57:52+08:00
symexec_status: 0
```

## Issue 2: manual return witnesses remained after successful symbolic execution

- Phenomenon: `symexec` succeeded, but `output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_proof_manual.v` contained two placeholders:

```coq
Lemma proof_of_is_multiple_return_wit_1 : is_multiple_return_wit_1.
Proof. Admitted.

Lemma proof_of_is_multiple_return_wit_2 : is_multiple_return_wit_2.
Proof. Admitted.
```

- Context: `is_multiple_return_wit_1` is the `return 1` branch with hypothesis `a_pre % b_pre = 0` and postcondition requiring an existential multiple witness. `is_multiple_return_wit_2` is the `return 0` branch with hypothesis `a_pre % b_pre <> 0` and postcondition requiring `forall q, a_pre <> q * b_pre`.
- Fix action: replaced the placeholders with assertion-level `Right`/`Exists` and `Left` proofs. The successful proof uses `Z.rem_divide` for the divisible branch and `Z.rem_mul` for the non-divisible branch.
- Result: the final `proof_manual.v` contains no `Admitted.` proof and no top-level `Axiom` declaration.

## Issue 3: first proof attempt supplied `Z.mod_divide` arguments in the wrong shape

- Phenomenon: the first compile replay failed in `is_multiple_proof_manual.v` at line 27:

```text
Error: The variable Hmod_to_div was not found in the current environment.
```

- Failing fragment:

```coq
destruct (Z.mod_divide a_pre b_pre) as [Hmod_to_div _].
assert (Hb_nonzero: b_pre <> 0) by lia.
pose proof (Hmod_to_div Hb_nonzero H) as [q Hq].
```

- Cause: `Z.mod_divide` takes the nonzero denominator proof before returning the iff. Destructing it without that proof did not bind a usable forward direction.
- Fix action: moved `assert (Hb_nonzero: b_pre <> 0) by lia` before destructing the divisibility lemma.
- Result: the proof advanced to the next, more precise notation mismatch.

## Issue 4: generated C `%` uses `Z.rem`, not `Z.modulo`

- Phenomenon: the second compile replay failed in `is_multiple_proof_manual.v` at line 27:

```text
The term "H" has type "a_pre % b_pre = 0" while it is expected to have type
 "a_pre mod b_pre = 0".
```

- Localization: a `coqtop` check under the generated imports and scopes reported:

```text
Notation "x % y" := (Z.rem x y) (default interpretation)
```

- Cause: the generated VC models the C remainder operator with `Z.rem`, while the attempted proof used Euclidean modulo lemmas `Z.mod_divide` and `Z.mod_mul`.
- Fix action: changed the manual proof to use `Z.rem_divide` and `Z.rem_mul`.
- Result: the next full compile replay succeeded:

```text
compile_start: 2026-04-22T18:01:04+08:00
compile_end: 2026-04-22T18:01:06+08:00
compile_status: 0
```

## Issue 5: full compile replay and cleanup were required after proof success

- Phenomenon: successful `symexec` and manual proof edits are not enough for Verify success; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must compile with the workspace-specific logical path, and generated Coq build artifacts must be removed.
- Fix action: compiled the generated chain from `QualifiedCProgramming/SeparationLogic` using the documented `COMPILE.md` load path and then removed non-`.v` files from `output/verify_20260422_175633_is_multiple/coq/`.
- Result: `is_multiple_goal_check.v` compiled successfully, `proof_manual.v` has no admitted proof, and `find .../coq -type f ! -name '*.v'` now returns no files.
