# Verify Issues

## Prior same-function blocker avoided with `by local` int-bound bridge

- Phenomenon: the historical workspace `output/verify_20260422_135349_count_digits` failed on the safety witness for `cnt++`.  After `pre_process; entailer!`, the remaining goal was:

```coq
cnt + 1 <= 2147483647
```

with hypotheses such as:

```coq
n > 0
0 <= cnt
cnt + n <= n_pre
0 <= n_pre
```

but without `n_pre <= INT_MAX`.  The premises admitted counterexamples with a huge mathematical `n_pre`, so the old proof could not soundly finish in Verify scope.

- Trigger in this workspace: the input contract is still only:

```c
/*@ Require
      0 <= n && emp
    Ensure
      count_digits_spec(n@pre, __return) && emp
*/
```

so the loop invariant must not assume an upper bound unless it is derived from the current C local store.

- Fix action: added the local bridge before branching, while the parameter `n` is still present as an `Int` local:

```c
/*@ n <= INT_MAX by local */
```

Then the loop invariant carries:

```c
n@pre <= INT_MAX &&
cnt + n <= n@pre
```

The body guard `n > 0` gives `cnt + 1 <= cnt + n <= n@pre <= INT_MAX`, which is enough for `cnt++` safety.

- Result: `symexec` succeeded and generated `count_digits_safety_wit_5` into `proof_auto.v` instead of leaving it as a manual blocker.  The full `goal_check.v` compile passed after manual proof of the remaining pure loop and return witnesses.

## Infix power notation must use `Zpower` in annotation

- Phenomenon: C annotation parsing does not accept infix `10 ^ cnt` in invariants.  The previous same-function workspace recorded:

```text
fatal error: Expected proposition in .../annotated/verify_20260422_135349_count_digits.c
```

for an invariant fragment like:

```c
10 ^ cnt * n <= n@pre
```

- Fix action in this workspace: declared and used the stable prefix form:

```c
/*@ Extern Coq (Zpower : Z -> Z -> Z) */
...
Zpower(10, cnt) * n <= n@pre &&
n@pre < Zpower(10, cnt) * (n + 1)
```

- Result: `symexec` completed successfully and generated nonempty Coq files:

```text
count_digits_goal.v
count_digits_proof_auto.v
count_digits_proof_manual.v
count_digits_goal_check.v
```

## Manual proof needed quotient and power helper lemmas

- Phenomenon: the generated manual obligations after successful `symexec` were:

```coq
proof_of_count_digits_entail_wit_2
proof_of_count_digits_entail_wit_3
proof_of_count_digits_return_wit_1
proof_of_count_digits_return_wit_2
```

`count_digits_entail_wit_3` is the loop preservation VC.  It must prove the invariant after `cnt + 1` and `n ÷ 10`, including interval bounds:

```coq
10 ^ (cnt + 1) * (n ÷ 10) <= n_pre
n_pre < 10 ^ (cnt + 1) * ((n ÷ 10) + 1)
```

- Fix action: added local lemmas in `coq/generated/count_digits_proof_manual.v`:

```coq
Lemma pow10_pos : forall c, 0 <= c -> 0 < 10 ^ c.
Lemma pow10_succ_mul : forall c, 0 <= c -> 10 ^ (c + 1) = 10 ^ c * 10.
Lemma div10_bounds_pos :
  forall n,
    0 < n ->
    0 <= n ÷ 10 /\
    n ÷ 10 <= n - 1 /\
    10 * (n ÷ 10) <= n /\
    n < 10 * (n ÷ 10 + 1).
```

The division lemma uses `Z.quot` / `Z.rem` because generated C integer division is printed as `÷`.

- Result: `count_digits_entail_wit_3` proved with `pre_process; entailer!`, the helper quotient bounds, and `nia`.

## Stale hypothesis number in return witness after strengthening invariant

- Phenomenon: the first full compile failed in `proof_of_count_digits_return_wit_2`:

```text
The term "H11" has type "0 <= 2147483647" while it is expected to have type
"cnt = 0".
```

- Cause: adding `n_pre <= INT_MAX` to the invariant shifted the generated hypothesis numbering after `pre_process; entailer!`.  The proof branch had constructed:

```coq
assert (cnt = 0) by lia.
```

but still specialized the zero-count invariant implication with the old hypothesis number.

- Fix action: changed:

```coq
specialize (H5 H11).
```

to:

```coq
specialize (H5 H14).
```

- Result: recompiling `original/count_digits.v`, `count_digits_goal.v`, `count_digits_proof_auto.v`, `count_digits_proof_manual.v`, and `count_digits_goal_check.v` succeeded.

## Final cleanup and verification status

- Symexec command used the active annotated file:

```text
QualifiedCProgramming/linux-binary/symexec
  --input-file=annotated/verify_20260423_121024_count_digits.c
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_121024_count_digits
```

- Symexec status:

```text
symexec_start: 2026-04-23 12:17:29 +0800
symexec_end: 2026-04-23 12:17:30 +0800
symexec_exit: 0
symexec_elapsed_seconds: 0.34
```

- Final checks:

```text
rg -n "Admitted\\.|^Axiom\\b|^Parameter\\b" coq/generated/count_digits_proof_manual.v
```

returned no matches.  After cleanup, `find output/verify_20260423_121024_count_digits/coq -type f ! -name '*.v'` and `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` both returned no files.
