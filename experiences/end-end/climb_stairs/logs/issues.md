# Verify Issues

## Missing loop invariant in active annotated C

- Phenomenon: the active annotated file initially copied the contract C exactly and had no `Inv` before `for (int i = 2; i <= n; i++)`. A loop without an invariant cannot give `symexec` a reusable summary for the scalar DP state.
- Trigger: target function `climb_stairs` computes Fibonacci-style stair counts with `prev2`, `prev1`, `cur`, and loop variable `i`, but the postcondition is stated through `climb_stairs_z(n@pre)`.
- Localization: `annotated/verify_20260422_131939_climb_stairs.c`, before the `for` loop.
- Fix: added a loop-head invariant preserving `n == n@pre`, bounds `2 <= i <= n + 1`, state equalities `prev2 == climb_stairs_z(i - 2)` and `prev1 == climb_stairs_z(i - 1)`, plus a two-case fact for `cur` because the initial loop head has `cur == 0` while later loop heads have `cur == climb_stairs_z(i - 1)`.
- Key annotation:

```c
/*@ Inv
      2 <= n && n <= 45 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      prev2 == climb_stairs_z(i - 2) &&
      prev1 == climb_stairs_z(i - 1) &&
      (i == 2 => cur == 0) &&
      (i > 2 => cur == climb_stairs_z(i - 1))
*/
for (int i = 2; i <= n; i++) {
    cur = prev1 + prev2;
    prev2 = prev1;
    prev1 = cur;
}
```

- Result: rerunning `symexec` with the canonical `--input-file`/`-slp` invocation succeeded and generated fresh `climb_stairs_goal.v`, `climb_stairs_proof_auto.v`, `climb_stairs_proof_manual.v`, and `climb_stairs_goal_check.v`.

## Optional Coq input was not structurally recursive

- Phenomenon: the first documented compile attempt failed before generated proof checking because `original/climb_stairs.v` did not compile.
- Trigger command shape: compiling from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths and `-Q "$ORIG" ""`.
- Error excerpt:

```text
File ".../output/verify_20260422_131939_climb_stairs/original/climb_stairs.v", line 5, characters 0-147:
Error:
Recursive definition of climb_stairs_nat is ill-formed.
...
Recursive call to climb_stairs_nat has principal argument equal to
"S k" instead of one of the following variables: "n0"
"k".
```

- Localization: the optional contract Coq file defines:

```coq
Fixpoint climb_stairs_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S O => 1
  | S (S k) => climb_stairs_nat (S k) + climb_stairs_nat k
  end.
```

- Fix: did not edit `input/climb_stairs.v` or `original/climb_stairs.v`. Added a workspace-local dependency at `coq/deps/climb_stairs.v` and compiled with `-Q "$DEPS" ""` before `-Q "$ORIG" ""`, so unqualified `Require Import climb_stairs` resolves to the workspace-local definition. The final version uses an explicit lookup table for `0..45`, matching the verified contract range and avoiding recursive computation blowup.
- Result: `coq/deps/climb_stairs.v` compiled and unblocked `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Manual proof iteration for bounded Fibonacci arithmetic

- Phenomenon: `symexec` left four manual obligations in `coq/generated/climb_stairs_proof_manual.v`: `safety_wit_7`, `entail_wit_1`, `entail_wit_2`, and `return_wit_1`.
- Key obligations:
  - `safety_wit_7` proves `prev1 + prev2` stays within C `int` range under `2 <= i <= n_pre <= 45`.
  - `entail_wit_2` proves loop invariant preservation, including the recurrence step.
  - `return_wit_1` proves the early branch `0 <= n_pre <= 1` returns `climb_stairs_z n_pre`.
- Initial failed proof action: a large 46-way disjunction tactic was too slow inside `proof_manual.v`. A later linear `Z.eq_dec` tactic still needed scalar substitution before range splitting; otherwise the goal remained in terms of `prev1 + prev2`.
- Useful proof-state excerpt after `pre_process; entailer!.`:

```coq
H4 : prev2 = climb_stairs_z (i - 2)
H5 : prev1 = climb_stairs_z (i - 1)
============================
-2147483648 <= prev1 + prev2
```

- Fix: changed the manual witnesses to substitute `prev1` and `prev2` from the invariant equalities and use the bounded lookup-table computation:

```coq
entailer!; subst prev1; subst prev2; split_small_range i.
```

- Additional adjustment: when `vm_compute` reduced arithmetic comparisons to constructors, some goals became comparison contradictions such as `Lt = Gt -> False`; the case tactic now runs `repeat split; try congruence; lia`.
- Result: `proof_manual.v` compiles, contains no `Admitted.`, and contains no added `Axiom`.

## Final compile and cleanup

- Compile setup: from `QualifiedCProgramming/SeparationLogic`, compile `coq/deps/climb_stairs.v`, then `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` with base `_CoqProject`-style `-R` paths plus:

```bash
EXTRA=(
  -Q "$DEPS" ""
  -Q "$ORIG" ""
  -R "$GEN" "SimpleC.EE.CAV.verify_20260422_131939_climb_stairs"
)
```

- Result: `goal_check.v` compiled successfully.
- Cleanup: removed all non-`.v` files under `output/verify_20260422_131939_climb_stairs/coq/` and removed any non-`.c`/non-`.v` files under `input/`.
