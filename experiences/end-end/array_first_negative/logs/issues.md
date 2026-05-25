# Verification Issues

## 2026-04-22 04:17 +0800 - Initial annotated copy lacked loop annotations

- Phenomenon: the active annotated file `annotated/verify_20260422_041638_array_first_negative.c` initially contained the contract but no `Inv` or post-loop `Assert` around the `for` loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        return i;
    }
}

return -1;
```

- Why this blocks verification: the postcondition for both return paths needs facts about the already-scanned prefix. On the early return path, the verifier must know all indices before `i` are nonnegative. On the final `return -1` path, it must know every index in `0 <= j < n` is nonnegative. Without an invariant, those prefix facts are not preserved across loop iterations.
- Fix action: before editing the annotated C, `logs/annotation_reasoning.md` was created with the control-point reasoning. The active annotated file was then updated with a loop invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] >= 0) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

and a loop-exit assertion immediately before `return -1`:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] >= 0) &&
      IntArray::full(a, n, l)
*/
return -1;
```

- Result: rerunning `QualifiedCProgramming/linux-binary/symexec` on the latest annotated file completed successfully and generated fresh `array_first_negative_goal.v`, `array_first_negative_proof_auto.v`, `array_first_negative_proof_manual.v`, and `array_first_negative_goal_check.v`.

## 2026-04-22 04:19 +0800 - First manual symexec shell command wrote scratch logs outside the workspace

- Phenomenon: the first `symexec` command used absolute generated-file arguments but was launched from `QualifiedCProgramming`, while the shell redirections for `logs/qcp_run.log` and `logs/symexec_timing.tmp` were relative. This created temporary scratch files under `QualifiedCProgramming/logs/` instead of the current verify workspace.
- Triggering command shape:

```bash
mkdir -p coq/generated logs
...
> logs/qcp_run.log 2>&1
```

with working directory `QualifiedCProgramming`.

- Fix action: removed the accidental scratch files and empty directories that this run created:

```text
QualifiedCProgramming/logs/qcp_run.log
QualifiedCProgramming/logs/symexec_timing.tmp
QualifiedCProgramming/logs/
QualifiedCProgramming/coq/
```

Then reran `symexec` with the current workspace `output/verify_20260422_041638_array_first_negative` as the shell working directory and absolute generated-file paths.
- Result: the corrected run kept `qcp_run.log` and timing data inside the workspace and exited with status `0`.

## 2026-04-22 04:20 +0800 - First Coq compile attempt used the wrong working directory

- Phenomenon: the first `coqc` compile attempt failed at `array_first_negative_goal.v` before compiling later files. `logs/compile_goal.log` reported:

```text
Warning: Cannot open unifysl [cannot-open-path,filesystem,default]
Warning: Cannot open sets [cannot-open-path,filesystem,default]
Warning: Cannot open compcert_lib [cannot-open-path,filesystem,default]
Warning: Cannot open auxlibs [cannot-open-path,filesystem,default]
...
Error: Cannot find a physical path bound to logical path
int_auto with prefix AUXLib.
```

- Cause: the compile command used the documented `_CoqProject` load paths, such as `-R auxlibs AUXLib`, but it was run from `QualifiedCProgramming`. Those directories are relative to `QualifiedCProgramming/SeparationLogic`, so Coq could not resolve the base libraries.
- Fix action: reran the same compile template from `QualifiedCProgramming/SeparationLogic` with the workspace-specific load path:

```bash
-R output/verify_20260422_041638_array_first_negative/coq/generated \
   SimpleC.EE.CAV.verify_20260422_041638_array_first_negative
```

- Result: `array_first_negative_goal.v`, `array_first_negative_proof_auto.v`, `array_first_negative_proof_manual.v`, and `array_first_negative_goal_check.v` all compiled with status `0`. The final timing log records `compile_goal_status: 0`, `compile_proof_auto_status: 0`, `compile_proof_manual_status: 0`, and `compile_goal_check_status: 0`.
