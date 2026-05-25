## 2026-04-22 16:34 +0800 - Missing loop invariant for scalar Fibonacci recurrence

- Phenomenon: the active annotated C initially matched the contract input and had no invariant before `for (i = 2; i <= n; ++i)`. Without an invariant, symbolic execution would not have a summary connecting the scalar loop state `(a, b, i)` to the postcondition `__return == fib_z(n@pre)`.
- Trigger: verifying `input/fibonacci.c`, whose loop updates `c = a + b; a = b; b = c;`.
- Localization: `annotated/verify_20260422_163304_fibonacci.c`, loop before line containing `for (i = 2; i <= n; ++i)`.
- Fix action: added an invariant at the real `for` control point:

```c
/*@ Inv
      1 <= n && n <= 46 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      a == fib_z(i - 2) &&
      b == fib_z(i - 1)
*/
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

- Why this fixes it: after the `n == 0` early return, the continuing path has `1 <= n`. Initially `i == 2`, `a == fib_z(0)`, and `b == fib_z(1)`. Each iteration shifts the pair to the next Fibonacci pair. On loop exit, `i > n` plus `i <= n + 1` gives `i == n + 1`, so `b == fib_z(i - 1) == fib_z(n@pre)`.
- Result: rerunning `symexec` on the latest annotated C succeeded and generated fresh `fibonacci_goal.v`, `fibonacci_proof_auto.v`, `fibonacci_proof_manual.v`, and `fibonacci_goal_check.v`.

## 2026-04-22 16:35 +0800 - Fresh symbolic execution required after annotation edit

- Phenomenon: after adding the invariant, generated Coq artifacts had to be recreated so the VCs matched the active annotated file.
- Trigger: verify workflow requires rerunning `symexec` after any `Inv`/`Assert` edit.
- Localization: `logs/qcp_run.log`, `logs/symexec_status.log`, and `logs/symexec_time.log`.
- Fix action: cleared stale generated targets and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_163304_fibonacci.c \
  --goal-file=output/verify_20260422_163304_fibonacci/coq/generated/fibonacci_goal.v \
  --proof-auto-file=output/verify_20260422_163304_fibonacci/coq/generated/fibonacci_proof_auto.v \
  --proof-manual-file=output/verify_20260422_163304_fibonacci/coq/generated/fibonacci_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_163304_fibonacci \
  --no-exec-info
```

- Result: `symexec_exit: 0`; `qcp_run.log` ended with `Successfully finished symbolic execution`; elapsed time was `0.06` seconds.

## 2026-04-22 16:36 +0800 - Manual Fibonacci arithmetic witnesses remained

- Phenomenon: successful `symexec` left four admitted obligations in `coq/generated/fibonacci_proof_manual.v`: `fibonacci_safety_wit_6`, `fibonacci_entail_wit_1`, `fibonacci_entail_wit_2`, and `fibonacci_return_wit_1`.
- Trigger: the recurrence and overflow facts depend on `fib_z` from the task-specific Coq file and are pure arithmetic/range obligations outside the automatic strategy.
- Localization: `coq/generated/fibonacci_goal.v` definitions:

```coq
Definition fibonacci_safety_wit_6 := ... 
  [| a = fib_z (i - 2) |] && [| b = fib_z (i - 1) |]
|-- [| a + b <= INT_MAX |] && [| INT_MIN <= a + b |].

Definition fibonacci_entail_wit_2 := ...
|-- ... [| b = fib_z (i + 1 - 2) |] &&
          [| a + b = fib_z (i + 1 - 1) |] ...
```

- Fix action: added local bounded helper lemmas to `fibonacci_proof_manual.v`:

```coq
Lemma fib_z_sum_int_bound_2_46 :
  forall i, 2 <= i -> i <= 46 ->
    INT_MIN <= fib_z (i - 2) + fib_z (i - 1) <= INT_MAX.

Lemma fib_z_step_2_46 :
  forall i, 2 <= i -> i <= 46 ->
    fib_z (i - 2) + fib_z (i - 1) = fib_z i.
```

- Result: the overflow and recurrence witnesses were discharged using those helpers with bounds solved by `lia`.

## 2026-04-22 16:38 +0800 - Direct `vm_compute` inside witness proof was too slow

- Phenomenon: the first proof script used bounded `vm_compute` directly inside `entailer!` for `safety_wit_6` and `entail_wit_2`. The full compile reached `fibonacci_proof_manual.v` and then ran for over 40 seconds without advancing.
- Trigger: repeated full computation in a larger separation-logic proof context.
- Localization: `logs/coq_compile.log` at interruption showed only:

```text
compile_start=2026-04-22T16:36:19+08:00
compiled=original/fibonacci.v
compiled=fibonacci_goal.v
compiled=fibonacci_proof_auto.v
```

- Fix action: moved bounded concrete Fibonacci computation into pure helper lemmas, then used those helpers from the main witnesses.
- Result: `fibonacci_proof_manual.v` compiled in isolation, and the later full compile completed through `fibonacci_goal_check.v`.

## 2026-04-22 16:40 +0800 - Undefined scalar-store weakening needed `StoreAux`

- Phenomenon: `fibonacci_entail_wit_2` left a heap weakening subgoal after `entailer!; subst a; subst b`:

```coq
&( "c") # Int |-> (fib_z (i - 2) + fib_z (i - 1)) |-- &( "c") # Int |-_
```

- Trigger: the invariant preservation VC forgets the temporary variable `c`; a concrete `Int` store must be weakened to an undefined `Int` store.
- Localization: `coq/generated/fibonacci_proof_manual.v`, proof of `proof_of_fibonacci_entail_wit_2`.
- Fix action: imported `StoreAux` and solved the first subgoal with:

```coq
sep_apply store_int_undef_store_int.
entailer!.
```

- Result: the heap weakening subgoal closed, leaving only the two pure Fibonacci equalities.

## 2026-04-22 16:41 +0800 - Return witness needed substitution before computation

- Phenomenon: `fibonacci_return_wit_1` failed with `Cannot find witness` when the proof tried `vm_compute; lia` after `entailer!`.
- Trigger: the remaining goal was `0 = fib_z n_pre` with hypothesis `H : n_pre = 0`; `vm_compute` cannot reduce `fib_z n_pre` while `n_pre` is still a variable.
- Localization: `coq/generated/fibonacci_proof_manual.v`, proof of `proof_of_fibonacci_return_wit_1`.
- Fix action: changed the proof to:

```coq
pre_process.
entailer!.
subst n_pre.
vm_compute.
lia.
```

- Result: `fibonacci_proof_manual.v` compiled successfully and contains no `Admitted.` or top-level `Axiom`.

## 2026-04-22 16:42 +0800 - Full compile and cleanup

- Compile setup: ran from `QualifiedCProgramming/SeparationLogic` with the stable base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_163304_fibonacci`.
- Compile result:

```text
compiled=original/fibonacci.v
compiled=fibonacci_goal.v
compiled=fibonacci_proof_auto.v
compiled=fibonacci_proof_manual.v
compiled=fibonacci_goal_check.v
compile_status=0
```

- Cleanup action: deleted non-`.v` files under `output/verify_20260422_163304_fibonacci/coq/`. `input/` had no non-`.c`/non-`.v` intermediate files to remove.
- Result: `coq/` now contains only `generated/fibonacci_goal.v`, `generated/fibonacci_proof_auto.v`, `generated/fibonacci_proof_manual.v`, and `generated/fibonacci_goal_check.v`.
