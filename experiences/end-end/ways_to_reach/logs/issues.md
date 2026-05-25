# Verify Issues

## Missing loop invariant for scalar recurrence

- Phenomenon: the active annotated C file initially matched `input/ways_to_reach.c` and had no `Inv` before the only loop:

```c
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

- Trigger: the postcondition is stated through the imported Coq function `ways_to_reach_z(n@pre)`, but without a loop invariant `symexec` would have no persistent relation between C locals `a`, `b`, `i`, and the Coq recurrence.
- Localization: `annotated/verify_20260423_054104_ways_to_reach.c`, immediately before `for (i = 2; i <= n; ++i)`.
- Fix: added a loop-head invariant using the real `for` control point after `i = 2` and before testing `i <= n`. The invariant preserves `n == n@pre`, bounds `2 <= i <= n + 1`, and accumulator meanings `a == ways_to_reach_z(i - 2)` and `b == ways_to_reach_z(i - 1)`.
- Key annotation:

```c
/*@ Inv
      1 <= n && n <= 45 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      a == ways_to_reach_z(i - 2) &&
      b == ways_to_reach_z(i - 1)
*/
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

- Result: rerunning `symexec` with the active annotated file completed successfully and generated fresh `ways_to_reach_goal.v`, `ways_to_reach_proof_auto.v`, `ways_to_reach_proof_manual.v`, and `ways_to_reach_goal_check.v`.

## Manual witnesses after successful symexec

- Phenomenon: after successful `symexec`, `coq/generated/ways_to_reach_proof_manual.v` contained four generated admitted obligations:

```coq
Lemma proof_of_ways_to_reach_safety_wit_6 : ways_to_reach_safety_wit_6.
Proof. Admitted.

Lemma proof_of_ways_to_reach_entail_wit_1 : ways_to_reach_entail_wit_1.
Proof. Admitted.

Lemma proof_of_ways_to_reach_entail_wit_2 : ways_to_reach_entail_wit_2.
Proof. Admitted.

Lemma proof_of_ways_to_reach_return_wit_1 : ways_to_reach_return_wit_1.
Proof. Admitted.
```

- Trigger: the remaining VCs were pure scalar recurrence and C integer-range obligations, plus one local-store cleanup obligation for `c`.
- Localization: `output/verify_20260423_054104_ways_to_reach/coq/generated/ways_to_reach_proof_manual.v`.
- Fix: added local helper lemmas proving the Coq recurrence step:

```coq
Lemma ways_to_reach_nat_step : forall n,
  ways_to_reach_nat (S (S n)) = ways_to_reach_nat (S n) + ways_to_reach_nat n.

Lemma ways_to_reach_z_step : forall z,
  2 <= z -> ways_to_reach_z z = ways_to_reach_z (z - 1) + ways_to_reach_z (z - 2).
```

and a bounded range helper:

```coq
Lemma ways_to_reach_z_bound_45 : forall z,
  0 <= z <= 45 -> 0 <= ways_to_reach_z z <= INT_MAX.
```

- Result: `safety_wit_6` rewrites `a + b` to `ways_to_reach_z i` and uses the bound; `entail_wit_1` is solved by `pre_process`; `entail_wit_2` uses `sep_apply (poly_store_poly_undef_store (&( "c")) FET_int (a + b))` followed by the recurrence equalities; `return_wit_1` computes the `n_pre = 0` branch. The manual proof file now contains no `Admitted.` and no added `Axiom`.

## Proof tactic iteration: overlong computation and store cleanup

- Phenomenon 1: the first manual proof edit used a broad `split_small_range` tactic with `vm_compute` directly inside the witness proofs. `coqc` spent over a minute compiling `ways_to_reach_proof_manual.v` with no output.
- Trigger snippet:

```coq
entailer!; subst a; subst b; split_small_range i.
```

- Fix: killed the long-running compile and replaced broad witness-level computation with the symbolic recurrence helper `ways_to_reach_z_step`. Computation is now limited to the pure bounded helper `ways_to_reach_z_bound_45`.
- Result: manual compile moved past the long-running normalization.

- Phenomenon 2: an intermediate `entail_wit_2` proof left the spatial goal:

```coq
&( "c") # Int |-> (ways_to_reach_z (i - 2) + ways_to_reach_z (i - 1))
|-- &( "c") # Int |->_
```

- Trigger: applying `entailer!` before the store-to-undef rule unfolded the store and left a low-level goal that did not match `poly_store_poly_undef_store`.
- Fix: applied the project lemma before the final pure proof:

```coq
sep_apply (poly_store_poly_undef_store (&( "c")) FET_int (a + b)).
entailer!; subst a; subst b.
```

- Result: only the two pure recurrence equalities remained, and the final explicit rewrite

```coq
rewrite (ways_to_reach_z_step i H2).
```

completed the preservation proof.

## Final compile and cleanup

- Compile command shape: from `QualifiedCProgramming/SeparationLogic`, compiled the task-specific original Coq file and then generated `goal`, `proof_auto`, `proof_manual`, and `goal_check` with the standard `_CoqProject` `-R` paths plus:

```bash
EXTRA=(
  -Q "$ORIG" ""
  -R "$GEN" "SimpleC.EE.CAV.verify_20260423_054104_ways_to_reach"
)
```

- Result: `ways_to_reach_goal.v`, `ways_to_reach_proof_auto.v`, `ways_to_reach_proof_manual.v`, and `ways_to_reach_goal_check.v` all compiled successfully; `logs/coq_compile.log` records `compile_status=0`.
- Cleanup: removed all non-`.v` files under `output/verify_20260423_054104_ways_to_reach/coq/`, removed Coq byproducts from workspace `original/`, and confirmed there were no non-`.c`/non-`.v` files under `input/`.
