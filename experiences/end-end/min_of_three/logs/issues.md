# Verify Issues

## Compile log path was initially relative to the wrong working directory

- Phenomenon: the first complete Coq compile command was executed from `QualifiedCProgramming/SeparationLogic`, as required by `experiences/general/COMPILE.md`, but the `tee` target was written as a relative path:

```text
tee: output/verify_20260422_204031_min_of_three/logs/compile.log: No such file or directory
compile_start=2026-04-22 20:42:47 +0800
compile_end=2026-04-22 20:42:49 +0800
compile_status=0
```

- Trigger: compile commands must run in the `SeparationLogic` directory so `_CoqProject`-style load paths resolve, while the task workspace is under `output/verify_20260422_204031_min_of_three`.
- Localization: the failed log write happened before `logs/compile.log` was created for this workspace. The Coq command sequence itself still returned `compile_status=0`.
- Fix action: reran the same compile sequence with an absolute workspace log path:

```text
tee "$WS/logs/compile.log"
```

- Result after fix: `output/verify_20260422_204031_min_of_three/logs/compile.log` was created and records:

```text
compile_start=2026-04-22 20:43:04 +0800
compile_end=2026-04-22 20:43:06 +0800
compile_status=0
```

## No annotation or manual proof repair was needed

- Symptom checked: the active annotated file `annotated/verify_20260422_204031_min_of_three.c` is the same straight-line branch program as the input:

```c
int m = a;
if (b < m) {
    m = b;
}
if (c < m) {
    m = c;
}
return m;
```

- Reason: there are no loops, heap predicates, or missing program-state facts that need `Inv`, `Assert`, `which implies`, or a loop-exit assertion. The two branch conditions give the four return cases needed for the contract.
- Evidence from `symexec`: `output/verify_20260422_204031_min_of_three/logs/qcp_run.log` ended with:

```text
End of symbolic execution of function min_of_three
Successfully finished symbolic execution
symexec_status=0
```

- Manual proof check: `coq/generated/min_of_three_proof_manual.v` contains only imports and no theorem body, so no manual witness was generated for this task. `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully in the final compile run.
