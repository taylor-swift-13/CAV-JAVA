# Verification Issues

## 2026-04-22 fibonacci_mod verification issues

### Issue 1: Missing loop invariant for scalar Fibonacci modulo loop

Symptom: the active annotated file initially had no `Inv` before `for (i = 2; i <= n; ++i)`, so symbolic execution would not have a loop summary connecting the final `return b` to `fib_mod_z(n@pre, mod@pre)`.

Triggering C fragment:

```c
for (i = 2; i <= n; ++i) {
    c = (a + b) % mod;
    a = b;
    b = c;
}

return b;
```

Fix: added one invariant in `annotated/verify_20260422_164639_fibonacci_mod.c` at the true `for` control point. The invariant records the unchanged parameters, the loop bounds, the modeled pair of adjacent residues, and residue range facts needed for `a + b` safety:

```c
/*@ Inv
      1 <= n && n < 2147483647 &&
      0 < mod && mod <= 1073741824 &&
      n == n@pre && mod == mod@pre &&
      2 <= i && i <= n + 1 &&
      a == fib_mod_z(i - 2, mod) &&
      b == fib_mod_z(i - 1, mod) &&
      0 <= a && a < mod &&
      0 <= b && b < mod
*/
```

Result: fresh symexec completed successfully and generated `fibonacci_mod_goal.v`, `fibonacci_mod_proof_auto.v`, `fibonacci_mod_proof_manual.v`, and `fibonacci_mod_goal_check.v`.

Relevant command result:

```text
Start to symbolic execution on program : annotated/verify_20260422_164639_fibonacci_mod.c
Symbolic Execution into function fibonacci_mod
End of symbolic execution of function fibonacci_mod
Successfully finished symbolic execution
symexec_exit: 0
```

### Issue 2: `fib_mod_z_step` initially used a brittle `Z.to_nat` rewrite

Symptom: the first manual proof attempt failed while compiling helper lemma `fib_mod_z_step`:

```text
File ".../fibonacci_mod_proof_manual.v", line 66, characters 4-32:
Error: Found no subterm matching "Z.to_nat (?M3177 + ?M3178)" in the current goal.
```

Cause: the proof tried to force `Z2Nat.inj_add` after replacing `Z.to_nat i`, but the natural-number equality subgoal no longer contained the exact syntactic term expected by `rewrite`.

Failed proof fragment:

```coq
replace i with ((i - 2) + 2) at 1 by lia.
rewrite Z2Nat.inj_add by lia.
simpl.
reflexivity.
```

Fix: proved the natural equality by applying `Nat2Z.inj` and simplifying both sides with `Z2Nat.id` and `Nat2Z.inj_succ`:

```coq
apply Nat2Z.inj.
rewrite Z2Nat.id by lia.
rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
rewrite Z2Nat.id by lia.
lia.
```

Result: the recurrence helper compiled and could be used in the loop-preservation witness.

### Issue 3: Manual witness scripts assumed the wrong `entailer!` subgoal order

Symptom: `proof_of_fibonacci_mod_entail_wit_1` failed with:

```text
Error: Found no subterm matching "fib_mod_z 0 ?M39747" in the current goal.
```

Cause: after `pre_process; entailer!.`, the base equalities had already been solved. The only remaining subgoals were:

```coq
1 % mod_pre < mod_pre
0 <= 1 % mod_pre
```

Fix: removed the unnecessary base-case rewrite bullets and discharged both remaining goals with `Z_rem_nonneg_bound 1 mod_pre` plus `lia`.

Result: `proof_of_fibonacci_mod_entail_wit_1` compiled.

### Issue 4: Bare recurrence rewrite could not infer helper arguments

Symptom: `proof_of_fibonacci_mod_entail_wit_2` later failed at the recurrence rewrite:

```text
Error: Tactic failure: Cannot find witness.
```

Failed fragment:

```coq
replace ((i + 1) - 1) with i by lia.
rewrite fib_mod_z_step by lia.
```

Cause: Coq could not infer the quantified arguments of `fib_mod_z_step` reliably from the rewrite target.

Fix: made the helper application explicit:

```coq
replace ((i + 1) - 1) with i by lia.
rewrite (fib_mod_z_step i mod_pre) by lia.
reflexivity.
```

Result: the full ordered compile succeeded through `fibonacci_mod_goal_check.v`:

```text
compiled=original/fibonacci_mod.v
compiled=fibonacci_mod_goal.v
compiled=fibonacci_mod_proof_auto.v
compiled=fibonacci_mod_proof_manual.v
compiled=fibonacci_mod_goal_check.v
compile_status=0
```
