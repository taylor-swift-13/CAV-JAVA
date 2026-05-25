# Verification Issues

## Missing loop invariant in active annotated C

- Phenomenon: the active annotated file `annotated/verify_20260422_054629_array_longest_nonnegative_run.c` initially copied the input contract but had no `Inv` before the only `while (i < n)` loop. Without an invariant, `symexec` would have no persistent relationship between `best`, `current`, the already processed prefix, and `array_longest_nonnegative_run_spec(l)`.
- Trigger: the loop updates two accumulators:

```c
while (i < n) {
    if (a[i] >= 0) {
        current++;
        if (current > best) {
            best = current;
        }
    } else {
        current = 0;
    }
    i++;
}
```

- Fix: added an invariant at the loop head:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      0 <= current && current <= i &&
      0 <= best && best <= i &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
        array_longest_nonnegative_run_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
```

- Additional fix: exposed the accumulator helper from the provided input `.v`:

```c
/*@ Extern Coq (array_longest_nonnegative_run_acc : Z -> Z -> list Z -> Z) */
```

- Result: `symexec` succeeded and generated `coq/generated/array_longest_nonnegative_run_goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Manual witnesses generated as admitted proofs

- Phenomenon: after successful `symexec`, `coq/generated/array_longest_nonnegative_run_proof_manual.v` contained five admitted manual witnesses:

```coq
Lemma proof_of_array_longest_nonnegative_run_entail_wit_1 : array_longest_nonnegative_run_entail_wit_1.
Proof. Admitted.
...
Lemma proof_of_array_longest_nonnegative_run_return_wit_1 : array_longest_nonnegative_run_return_wit_1.
Proof. Admitted.
```

- Trigger: the branch-preservation witnesses require rewriting the unprocessed suffix:

```coq
sublist i n_pre l = Znth i l 0 :: sublist (i + 1) n_pre l
```

and then simplifying one step of `array_longest_nonnegative_run_acc`.
- Fix: added local helper lemma `sublist_head_cons_Z` in `proof_manual.v` and proved:
  - `entail_wit_1` by unfolding `array_longest_nonnegative_run_spec` and rewriting `sublist_self`;
  - `entail_wit_2_1` by reducing the nonnegative branch and rewriting `Z.max best (current + 1)` to `current + 1`;
  - `entail_wit_2_2` by reducing the nonnegative branch and rewriting `Z.max best (current + 1)` to `best`;
  - `entail_wit_2_3` by reducing the negative branch to accumulator state `(0, best)`;
  - `return_wit_1` by deriving `i = n_pre`, rewriting `sublist n_pre n_pre l` to `nil`, and simplifying the accumulator.
- Result: `proof_manual.v` contains no `Admitted.` and no added `Axiom`.

## Initial compile attempted from the wrong working directory

- Phenomenon: the first full `coqc` replay failed while compiling `array_longest_nonnegative_run_goal.v`:

```text
Error: Cannot find a physical path bound to logical path
int_auto with prefix AUXLib.
```

- Trigger: the compile command used the `_CoqProject` `-R` entries from `QualifiedCProgramming`, but those relative paths are valid from `QualifiedCProgramming/SeparationLogic`.
- Fix: reran the same compile template from `QualifiedCProgramming/SeparationLogic`, with the workspace-specific load paths:

```bash
-Q "$ORIG" ""
-R "$GEN" "SimpleC.EE.CAV.verify_20260422_054629_array_longest_nonnegative_run"
```

- Result: `logs/coq_compile.log` records successful compilation of:
  - `original/array_longest_nonnegative_run.v`
  - `coq/generated/array_longest_nonnegative_run_goal.v`
  - `coq/generated/array_longest_nonnegative_run_proof_auto.v`
  - `coq/generated/array_longest_nonnegative_run_proof_manual.v`
  - `coq/generated/array_longest_nonnegative_run_goal_check.v`

## Coq intermediate cleanup

- Phenomenon: successful compilation left `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Fix: removed all non-`.v` files under `coq/` with:

```bash
find coq -type f ! -name '*.v' -delete
```

- Result: `find coq -type f ! -name '*.v'` returned no files after cleanup.
