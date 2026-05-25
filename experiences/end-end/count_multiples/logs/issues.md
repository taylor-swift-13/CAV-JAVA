# Verify Issues

## 2026-04-22 15:24 CST - Active input had no loop invariant for the scalar counting loop

- Phenomenon: the active annotated copy initially had no `Inv` before the only loop:

```c
int i;
int cnt = 0;

for (i = 1; i <= n; ++i) {
    if (i % k == 0) {
        cnt++;
    }
}

return cnt;
```

- Trigger: the postcondition required `__return == count_multiples_spec(n@pre, k@pre)`, but no annotation connected `cnt` to the Coq recurrence `count_multiples_upto`.
- Location: `annotated/verify_20260422_152433_count_multiples.c`, before the `for (i = 1; i <= n; ++i)` loop.
- Fix: added a workspace helper `coq/deps/count_multiples_helper.v`:

```coq
Definition count_multiples_upto_z (k fuel : Z) : Z :=
  count_multiples_upto k (Z.to_nat fuel).
```

and imported it in the active annotated C with:

```c
/*@ Extern Coq (count_multiples_upto_z : Z -> Z -> Z) */
/*@ Import Coq Require Import count_multiples_helper */
```

Then added the loop invariant:

```c
/*@ Inv
      1 <= n && n < INT_MAX &&
      1 <= k &&
      n == n@pre &&
      k == k@pre &&
      1 <= i && i <= n + 1 &&
      0 <= cnt && cnt <= i - 1 && cnt <= n &&
      cnt == count_multiples_upto_z(k, i - 1)
*/
```

and a loop-exit assertion:

```c
/*@ Assert
      i == n + 1 &&
      n == n@pre &&
      k == k@pre &&
      cnt == count_multiples_spec(n@pre, k@pre)
*/
```

- Result: after clearing stale generated files, `symexec` succeeded and produced `count_multiples_goal.v`, `count_multiples_proof_auto.v`, `count_multiples_proof_manual.v`, and `count_multiples_goal_check.v`.

## 2026-04-22 15:28 CST - Manual helper lemma used ambiguous infix `%`

- Phenomenon: the first full Coq compile failed in `coq/generated/count_multiples_proof_manual.v`:

```text
File ".../count_multiples_proof_manual.v", line 35, characters 4-9:
Error: Unknown scope delimiting key k.
```

- Trigger: the manually added helper lemma statement used `i % k = 0`. In ordinary Coq parsing, this was treated as a scope delimiter form rather than the generated C remainder notation.
- Location: `coq/generated/count_multiples_proof_manual.v`, helper lemmas `count_multiples_upto_z_step_multiple` and `count_multiples_upto_z_step_not_multiple`.
- Fix: changed the helper assumptions to use explicit Coq remainder:

```coq
Z.rem i k = 0
Z.rem i k <> 0
```

The proof body already destructed `Z.eq_dec (Z.rem i k) 0`, so the change only made the statement parse unambiguously.
- Result: recompiling after the edit succeeded through `count_multiples_goal_check.v`.

## 2026-04-22 15:29 CST - Final cleanup of Coq build artifacts

- Phenomenon: successful Coq compilation left `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under the workspace `coq/` tree.
- Trigger: normal `coqc` output from compiling `coq/deps/count_multiples_helper.v` and the generated Coq files.
- Fix: deleted all non-`.v` files under `output/verify_20260422_152433_count_multiples/coq/` and checked that `input/` had no non-`.c`/non-`.v` files.
- Result: cleanup check returned no remaining non-`.v` files under workspace `coq/`, and no forbidden intermediate files under `input/`.
