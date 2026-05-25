# Verify Issues

## 2026-04-22 annotation needed for scalar exponentiation loop

- Phenomenon: the input C had a `for (i = 0; i < exp; ++i)` loop but no loop invariant or intermediate assertions, so the verifier had no explicit relationship between the loop counter `i`, accumulator `ans`, and the mathematical specification `power_nonnegative_z(base@pre, exp@pre)`.
- Triggering source snippet:

```c
int i;
int ans = 1;

for (i = 0; i < exp; ++i) {
    ans = ans * base;
}

return ans;
```

- Fix action: added the invariant in the active annotated copy `annotated/verify_20260422_205655_power_nonnegative.c`, not in `input/`. The key invariant state is:

```c
/*@ Inv
      0 <= i && i <= exp &&
      base == base@pre &&
      exp == exp@pre &&
      ans == power_nonnegative_z(base@pre, i) &&
      (forall (k: Z), (0 <= k && k <= exp@pre) =>
        (INT_MIN <= power_nonnegative_z(base@pre, k) &&
         power_nonnegative_z(base@pre, k) <= INT_MAX))
*/
```

- Why this fixed the symbolic state: at the loop head, `i` is the completed exponent prefix. Initialization uses `i = 0` and `ans = 1`; preservation after one body iteration is the recurrence `power_nonnegative_z(base, i + 1) = power_nonnegative_z(base, i) * base`; exit combines `i >= exp` with `i <= exp` to recover `i == exp`.
- Result: a fresh `symexec` run succeeded and generated `power_nonnegative_goal.v`, `power_nonnegative_proof_auto.v`, `power_nonnegative_proof_manual.v`, and `power_nonnegative_goal_check.v`.

## 2026-04-22 manual proof required for power recurrence and overflow bound

- Phenomenon: successful `symexec` generated three manual proof placeholders in `output/verify_20260422_205655_power_nonnegative/coq/generated/power_nonnegative_proof_manual.v`:

```coq
Lemma proof_of_power_nonnegative_safety_wit_3 : power_nonnegative_safety_wit_3.
Proof. Admitted.

Lemma proof_of_power_nonnegative_entail_wit_1 : power_nonnegative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_power_nonnegative_entail_wit_3 : power_nonnegative_entail_wit_3.
Proof. Admitted.
```

- Root cause: the generated VCs need the Coq-side recurrence for the task-specific definition:

```coq
power_nonnegative_z base (i + 1) =
power_nonnegative_z base i * base
```

The recurrence is true for `0 <= i` after unfolding `power_nonnegative_z` and rewriting `Z.to_nat (i + 1)`.

- Fix action: added a local helper lemma in `power_nonnegative_proof_manual.v`:

```coq
Lemma power_nonnegative_z_succ:
  forall base i,
    0 <= i ->
    power_nonnegative_z base (i + 1) =
    power_nonnegative_z base i * base.
```

Then:
  - `proof_of_power_nonnegative_safety_wit_3` rewrites the multiplication to `power_nonnegative_z base_pre (i + 1)`, invokes `entailer!`, and instantiates the contract range hypothesis at `i + 1`.
  - `proof_of_power_nonnegative_entail_wit_1` is solved by `pre_process`.
  - `proof_of_power_nonnegative_entail_wit_3` uses the same recurrence rewrite to align the updated `ans` heap cell with the post-assignment assertion.

- Result: `power_nonnegative_proof_manual.v` contains no `Admitted.` and no local `Axiom` declaration. The full compile sequence completed successfully through `power_nonnegative_goal_check.v`.

## 2026-04-22 cleanup after successful compile

- Phenomenon: compiling the generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260422_205655_power_nonnegative/coq/generated/`.
- Fix action: deleted all non-`.v` files under the workspace `coq/` directory after successful `goal_check` compilation. Also removed Coq compiler artifacts from `original/` so that only the copied `.c` and `.v` inputs remain there.
- Result: `find output/verify_20260422_205655_power_nonnegative/coq -type f ! -name '*.v'` prints no files. `input/` also has no non-`.c`/non-`.v` generated files.
