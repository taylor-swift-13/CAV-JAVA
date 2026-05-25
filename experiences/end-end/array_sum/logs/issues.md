# Verify Issues

## 2026-04-22 08:40 +0800 - Missing loop invariant for read-only array prefix sum

- Phenomenon: the active annotated C initially copied the input file and had no `Inv` before the only `for (i = 0; i < n; ++i)` loop. Without an invariant, `symexec` would not have a persistent relation between the accumulator `ret` and the already processed prefix of ghost list `l`.
- Trigger: the contract requires `__return == sum(l)` and preservation of `IntArray::full(a, n, l)`, while the loop only updates `ret` and advances `i`.
- Location: `annotated/verify_20260422_084036_array_sum.c`.
- Fix action: added a loop invariant at the `for` guard control point:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      ret == sum(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

and added a loop-exit assertion immediately after the loop:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      ret == sum(l) &&
      IntArray::full(a, n, l)
*/
```

- Result: rerunning `symexec` against the current annotated file succeeded and generated fresh `array_sum_goal.v`, `array_sum_proof_auto.v`, `array_sum_proof_manual.v`, and `array_sum_goal_check.v`. The relevant log ending in `logs/qcp_run.log` was:

```text
End of symbolic execution of function array_sum
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 08:44 +0800 - Manual proof needed signed prefix-sum bounds

- Phenomenon: after successful `symexec`, `coq/generated/array_sum_proof_manual.v` contained four admitted manual obligations:

```coq
proof_of_array_sum_safety_wit_3
proof_of_array_sum_entail_wit_1
proof_of_array_sum_entail_wit_2
proof_of_array_sum_entail_wit_3
```

- Trigger: `array_sum_safety_wit_3` had to prove the C-int safety of `ret + Znth i l 0`. The invariant gave `ret = sum(sublist 0 i l)`, but the proof still needed to derive a concrete bound for the next prefix sum from the element bound `-10000 <= l[k] <= 10000` and `n <= 10000`.
- Key generated goal shape:

```coq
ret = sum (sublist 0 i l) ->
i < n_pre ->
n_pre <= 10000 ->
Zlength l = n_pre ->
(forall k, 0 <= k < n_pre -> -10000 <= Znth k l 0 <= 10000) ->
ret + Znth i l 0 <= INT_MAX /\ INT_MIN <= ret + Znth i l 0
```

- Fix action: added two local helper lemmas in `coq/generated/array_sum_proof_manual.v`:

```coq
Lemma sum_bound_signed_10000 :
  forall (l : list Z),
    (forall i, 0 <= i < Zlength l ->
      -10000 <= Znth i l 0 <= 10000) ->
    -10000 * Zlength l <= sum l <= 10000 * Zlength l.

Lemma sum_sublist_snoc :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sum (sublist 0 (i + 1) l) =
      sum (sublist 0 i l) + Znth i l 0.
```

The safety witness rewrites `ret + Znth i l 0` to `sum(sublist 0 (i + 1) l)`, applies the signed bound helper to the prefix, rewrites `Zlength(sublist 0 (i + 1) l)` to `i + 1`, and uses `i + 1 <= n_pre <= 10000` to show the value is within `INT_MIN..INT_MAX`.

- Result: `array_sum_proof_manual.v` compiles with no `Admitted.` and no newly added `Axiom`.

## 2026-04-22 08:44 +0800 - First compile wrapper did not fail fast

- Phenomenon: the first full compile shell group printed misleading later lines after `coqc` had already failed:

```text
Error: Syntax error: [equality_intropattern] ...
compiled array_sum_proof_manual.v
Error: Cannot find a physical path bound to logical path array_sum_proof_manual ...
compiled array_sum_goal_check.v
```

- Trigger: the shell group was piped to `tee` without `set -e`, so failures inside the group did not stop later commands.
- Fix action: reran compilation with `set -euo pipefail` and the documented load path template from `QualifiedCProgramming/SeparationLogic`.
- Result: subsequent compile runs stopped at the first real error, making the actual proof failures clear.

## 2026-04-22 08:45 +0800 - Coq proof syntax and simplification adjustments

- Phenomenon: early helper-proof versions failed with several concrete Coq errors:

```text
Syntax error: [equality_intropattern] ... expected after 'as'
Found no subterm matching "Zlength nil" in the current goal
Tactic failure: Cannot find witness
Found no subterm matching "10000" in the current goal
```

- Trigger: the initial helper used a compact `induction l as [| x xs IH]` pattern and `simpl` in a goal containing multiplication by `Zlength`. In this context, `simpl` unfolded `Z.mul` over symbolic `Zlength`, producing large `match` expressions that `lia`/`nia` did not close. The proof also initially used wrong generated hypothesis numbers in `entail_wit_3`.
- Fix action: rewrote the helper proof in conservative style with `intros l Hrange; induction l`, used `change (sum (a :: l)) with (a + sum l)` instead of broad `simpl`, added explicit `Zlength_cons`/`Zlength_sublist` side-condition proofs, and corrected the final exit proof to rewrite with `H5 : Zlength l = n_pre`.
- Result: the final full compile log shows:

```text
compiled array_sum_goal.v
compiled array_sum_proof_auto.v
compiled array_sum_proof_manual.v
compiled array_sum_goal_check.v
```
