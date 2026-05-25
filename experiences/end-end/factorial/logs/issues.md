# Verification Issues

## 2026-04-22 16:19 +0800 - Fingerprint initialized from empty placeholders

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`, which violates the verify workflow requirement to make retrieval metadata usable early in the task.
- Trigger: workspace initialization created the JSON skeleton before semantic classification.
- Localization: `output/verify_20260422_161944_factorial/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled `semantic_description` and used only controlled vocabulary values: `factorial`, `for_loop`, `scalar_only`, `compute_factorial`, `loop_invariant`, `pure_arithmetic`, `range_bound`, `nonnegative_input`, `overflow_guard`, `monotone_accumulator`, `int_range`, `empty_loop_possible`, and `manual_witness_needed`.
- Result: the fingerprint is now non-empty and retrieval-safe.

## 2026-04-22 16:20 +0800 - Active annotated file lacked the loop invariant required for factorial

- Phenomenon: the active annotated C only had the function contract; the loop had no `Inv`, no bridge assertion around multiplication, and no loop-exit assertion. Without those facts, the verifier would not retain `res == factorial(n@pre)` across the `for` loop.
- Trigger: original active file:

```c
int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
{
    int i;
    int res = 1;

    for (i = 1; i <= n; ++i) {
        res = res * i;
    }

    return res;
}
```

- Localization: `annotated/verify_20260422_161944_factorial.c`.
- Fix action: after recording detailed invariant reasoning in `logs/annotation_reasoning.md`, added the loop-head invariant, pre/post multiplication bridge assertions, and the loop-exit assertion:

```c
/*@ Inv
      1 <= i && i <= n + 1 && n == n@pre && res == factorial(i - 1)
*/
for (i = 1; i <= n; ++i) {
    /*@ 1 <= i && i <= n@pre && n == n@pre && res == factorial(i - 1) */
    res = res * i;
    /*@ 1 <= i && i <= n@pre && n == n@pre && res == factorial(i) */
}

/*@ i == n@pre + 1 && res == factorial(n@pre) */
return res;
```

- Result: the annotation shape is the standard scalar factorial loop invariant. The next step was a mandatory fresh `symexec` run.

## 2026-04-22 16:21 +0800 - Symexec failed before VC generation due to `factorial` symbol collision

- Phenomenon: after clearing generated files and running `symexec`, the tool failed before generating usable Coq goals. It created zero-byte `.v` files, then exited with status 1.
- Trigger: the input contract declares a Coq symbol named `factorial`, and the C function is also named `factorial`:

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
```

- Localization:
  - active C: `annotated/verify_20260422_161944_factorial.c`
  - run log: `output/verify_20260422_161944_factorial/logs/qcp_run.log`
- Command:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_161944_factorial.c \
  --goal-file=output/verify_20260422_161944_factorial/coq/generated/factorial_goal.v \
  --proof-auto-file=output/verify_20260422_161944_factorial/coq/generated/factorial_proof_auto.v \
  --proof-manual-file=output/verify_20260422_161944_factorial/coq/generated/factorial_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_161944_factorial \
  --no-exec-info
```

- Error excerpt:

```text
fatal error: Redefinition of `factorial' as different kind of symbol in annotated/verify_20260422_161944_factorial.c:11:1
symexec_status=1
```

- Diagnosis: this is not an invariant, assertion, or Coq proof failure. It is a front-end symbol table collision before symbolic execution begins. The archived successful factorial verification avoided the issue by naming the C function `fac` while keeping `Extern Coq (factorial: Z -> Z)`. In this task, repairing the collision would require either renaming the target C function or changing the mathematical Coq symbol used by `Ensure`; both are outside the normal Verify boundary because Verify should not redesign the interface or rewrite the contract.
- Fix action: did not rename the function and did not rewrite `Require` / `Ensure`. Removed the zero-byte generated `.v` files left by the failed run so the workspace does not contain misleading generated artifacts.
- Result: verification is blocked at the Contract/input level. No `goal.v`, `proof_auto.v`, `proof_manual.v`, or `goal_check.v` exists for a successful symexec run.

## 2026-04-22 16:25 +0800 - Retry repaired the `factorial` symbol collision in the annotated copy

- Phenomenon: the same workspace retry started from the previous blocker: `symexec` could not generate Coq VCs because the active annotated file declared both `Extern Coq (factorial: Z -> Z)` and `int factorial(int n)`.
- Triggering source fragment in `annotated/verify_20260422_161944_factorial.c` before the retry edit:

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
```

- Existing error evidence in `output/verify_20260422_161944_factorial/logs/qcp_run.log`:

```text
fatal error: Redefinition of `factorial' as different kind of symbol in annotated/verify_20260422_161944_factorial.c:11:1
symexec_status=1
```

- Fix action: after appending `output/verify_20260422_161944_factorial/logs/continue.md` and recording annotation reasoning, changed only the active annotated copy's C implementation symbol to avoid the front-end collision:

```c
/*@ Extern Coq (factorial: Z -> Z) */

int fac(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
```

The official input `input/factorial.c` was not modified. The mathematical contract expression `factorial(n@pre)` and all loop assertions over `factorial` were preserved.

- Result: rerunning `symexec` in the same workspace succeeded:

```text
Symbolic Execution into function fac
End of symbolic execution of function fac
Successfully finished symbolic execution
symexec_retry_status=0
```

It generated `factorial_goal.v`, `factorial_proof_auto.v`, `factorial_proof_manual.v`, and `factorial_goal_check.v`.

## 2026-04-22 16:27 +0800 - Manual factorial witnesses completed from archived matching proof shape

- Phenomenon: generated `output/verify_20260422_161944_factorial/coq/generated/factorial_proof_manual.v` contained three unfinished manual lemmas:

```coq
Lemma proof_of_fac_safety_wit_3 : fac_safety_wit_3.
Proof. Admitted.

Lemma proof_of_fac_entail_wit_1 : fac_entail_wit_1.
Proof. Admitted.

Lemma proof_of_fac_entail_wit_3 : fac_entail_wit_3.
Proof. Admitted.
```

- Localization:
  - `fac_safety_wit_3`: multiplication overflow side condition for `(factorial (i - 1)) * i` with `1 <= i <= n_pre <= 10`.
  - `fac_entail_wit_1`: invariant initialization, including `1 = factorial (1 - 1)`.
  - `fac_entail_wit_3`: assignment bridge from `(factorial (i - 1)) * i` to `factorial i`.
- Fix action: reused the archived matching proof pattern from `CAV/archieve/output_backup_20260422_011624/verify_20260414_153520_factorial/coq/generated/factorial_proof_manual.v`. The safety witness performs finite case splitting on `i = 1..10` and discharges each computed bound with `vm_compute`; `fac_entail_wit_3` rewrites `i` as `(i - 1) + 1` and applies `factorial_inc`.
- Result: `factorial_proof_manual.v` no longer contains `Admitted.` or any local `Axiom` declaration. The full compile sequence succeeded:

```text
compiled factorial_goal.v
compiled factorial_proof_auto.v
compiled factorial_proof_manual.v
compiled factorial_goal_check.v
compile_retry_status=0
```

After compilation, all non-`.v` Coq intermediates under `output/verify_20260422_161944_factorial/coq` were deleted. There were no non-`.c`/non-`.v` intermediates under `./input`.
