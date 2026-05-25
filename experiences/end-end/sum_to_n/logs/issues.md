## 2026-04-23 05:13 +0800 - Verification issues and fixes

### Missing loop invariant in active annotated C

- Symptom: the active annotated C initially copied `input/sum_to_n.c` with no `Inv` or post-loop assertion:

```c
for (i = 1; i <= n; ++i) {
    ret += i;
}

return ret;
```

- Trigger: `sum_to_n` is a scalar accumulation loop. Without a loop-head invariant, the verifier cannot preserve the relation between `ret` and the processed prefix `1..i-1`, and the return witness has no way to derive `ret == n@pre * (n@pre + 1) / 2`.
- Fix action: added the loop-head invariant in `annotated/verify_20260423_050130_sum_to_n.c`:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      n == n@pre &&
      ret == (i - 1) * i / 2
*/
```

The lower bound uses `1 <= i` and the upper bound uses `i <= n + 1`, which is valid even for the skip-loop case `n == 0`. The invariant also keeps `n == n@pre` for the postcondition. Added body assertions around `ret += i` and a loop-exit assertion:

```c
/*@ i == n@pre + 1 &&
    n == n@pre &&
    ret == n@pre * (n@pre + 1) / 2
*/
```

- Result: `symexec` completed successfully and generated `sum_to_n_goal.v`, `sum_to_n_proof_auto.v`, `sum_to_n_proof_manual.v`, and `sum_to_n_goal_check.v`.

### Manual witnesses needed quotient arithmetic helpers

- Symptom: `sum_to_n_proof_manual.v` initially contained six admitted manual witnesses:

```coq
proof_of_sum_to_n_safety_wit_3
proof_of_sum_to_n_safety_wit_4
proof_of_sum_to_n_entail_wit_1
proof_of_sum_to_n_entail_wit_3
proof_of_sum_to_n_entail_wit_4
proof_of_sum_to_n_entail_wit_5
```

- Trigger: generated C division appears as Coq `Z.quot` (`÷`). The key preservation fact

```coq
((i - 1) * i) ÷ 2 + i = (i * (i + 1)) ÷ 2
```

is not closed by plain `lia` or `nia`.
- Fix action: added local helper lemmas to `coq/generated/sum_to_n_proof_manual.v`:

```coq
sum_to_n_consecutive_product_even
sum_to_n_half_consecutive_exact
sum_to_n_triangular_step
sum_to_n_triangular_mono
sum_to_n_succ_bound_from_tri
```

These prove exact division by 2 for consecutive products, the triangular update step, monotonicity of the closed form, and the `++i` signed-int upper bound from the precondition overflow guard.
- Result: all six manual witnesses were completed with no `Admitted.` or new `Axiom` in `sum_to_n_proof_manual.v`.

### Coq proof-script structure issues during iteration

- Symptom: early compile attempts failed with proof-script errors rather than semantic failures:

```text
Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
No such goal. Focus next goal with bullet -.
Wrong bullet -: No more goals.
```

- Trigger: compact tactic forms such as `apply Z.quot_unique_exact; [lia|].` were rejected, and some witnesses were over-scripted after `pre_process` or `entailer!` had already solved a side goal.
- Fix action: rewrote quotient helper applications with explicit bullets, removed redundant `entailer!` from `proof_of_sum_to_n_entail_wit_1`, removed an extra bullet in `proof_of_sum_to_n_safety_wit_4`, and normalized simple expressions with local `replace ... by lia` steps where needed:

```coq
replace (i + 1 - 1) with i by lia.
reflexivity.
```

- Result: the final compile command completed with `compile_status=0`, including `sum_to_n_goal_check.v`.

### Final compile and cleanup

- Command shape: compiled from `QualifiedCProgramming/SeparationLogic` with the standard base `-R` load paths plus:

```bash
-Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260423_050130_sum_to_n
```

- Result: `sum_to_n_goal.v`, `sum_to_n_proof_auto.v`, `sum_to_n_proof_manual.v`, and `sum_to_n_goal_check.v` all compiled successfully.
- Cleanup: removed all non-`.v` files under `output/verify_20260423_050130_sum_to_n/coq/`. No non-`.c`/`.v` files were present under `input/`.
