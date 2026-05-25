## Iteration 1: add the semantic loop invariant for digit_sum

Program point: the only loop is `while (n > 0)` in `annotated/verify_20260422_154652_digit_sum.c`. The active annotated file currently has no loop invariant:

```c
int sum = 0;

while (n > 0) {
    sum += n % 10;
    n = n / 10;
}

return sum;
```

Without an invariant, symbolic execution has no stable relation between the original input `n@pre`, the shrinking loop variable `n`, and the accumulated `sum`. The postcondition requires `__return == digit_sum_z(n@pre)`, but after the loop the program only has the current local variables `sum` and `n`. The missing fact is that the already processed decimal suffix contributes `sum`, and the not-yet-processed prefix contributes `digit_sum_z(n)`.

The invariant to add immediately before the loop is:

```c
/*@ Inv
      0 <= n &&
      0 <= sum &&
      sum <= n@pre &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
while (n > 0) {
```

Why this is the right control-point state:

- Initialization: before the first loop test, `sum == 0` and `n == n@pre`, so `sum + digit_sum_z(n) == digit_sum_z(n@pre)` holds directly. The precondition gives `0 <= n`, and `0 <= sum` plus `sum <= n@pre` follow from `sum == 0` and `0 <= n@pre`.
- Preservation: in a loop body with `n > 0`, `sum += n % 10` records the current least significant decimal digit and `n = n / 10` removes it. The semantic preservation condition is exactly `digit_sum_z(old_n) == old_n % 10 + digit_sum_z(old_n / 10)`, so the invariant relation should be re-established for the next loop test. The nonnegative and accumulator bound facts are needed for C arithmetic safety and to keep the pure side conditions small.
- Exit usability: when the loop exits, the loop condition gives `n <= 0` while the invariant gives `0 <= n`, hence `n == 0`. The imported Coq definition makes `digit_sum_z(0) == 0`, so the invariant reduces to `sum == digit_sum_z(n@pre)`, which is exactly the return postcondition.

No separate loop-exit assertion is added in this first iteration. If symbolic execution or the generated return witness cannot recover `n == 0` and `digit_sum_z(0) == 0` from the invariant plus exit condition, the next annotation iteration should add the smallest assertion immediately after the loop rather than changing the contract.

## Iteration 2: strengthen the accumulator bound for C integer safety

After rerunning symbolic execution, the generated manual proof obligations include:

```coq
Definition digit_sum_safety_wit_3 :=
forall (n_pre: Z) (sum: Z) (n: Z),
  [| (n > 0) |] &&
  [| (0 <= n) |] &&
  [| (0 <= sum) |] &&
  [| (sum <= n_pre) |] &&
  [| ((sum + digit_sum_z n) = digit_sum_z n_pre) |] &&
  [| (0 <= n_pre) |] && ...
|--
  [| ((sum + (n % 10)) <= INT_MAX) |] && ...
```

The current invariant bound `sum <= n@pre` is too weak for this safety VC because the next C statement computes `sum + n % 10`. The proof needs a direct way to show `sum + n % 10 <= INT_MAX`. Since `0 <= n` and `0 <= n % 10 <= n` when `n > 0`, a better loop-state bound is `sum + n <= n@pre`. At the loop head, `sum` accounts for processed low-order digits and `n` is the remaining high-order prefix, so `sum + n <= n@pre` is true initially and is preserved because `(n % 10) + (n / 10) <= n` for positive decimal division.

I will replace:

```c
0 <= sum &&
sum <= n@pre &&
sum + digit_sum_z(n) == digit_sum_z(n@pre)
```

with:

```c
0 <= sum &&
sum + n <= n@pre &&
sum + digit_sum_z(n) == digit_sum_z(n@pre)
```

This is a semantic strengthening, not a contract change. It keeps the same exit path to the postcondition, and it gives the generated safety witness a reusable arithmetic fact for `sum += n % 10`.

## Iteration 3: preserve the pre-state integer upper bound explicitly

During manual proof of `digit_sum_safety_wit_3`, `entailer!` left the upper-bound subgoal:

```coq
sum + n % 10 <= INT_MAX
```

with only these relevant pure facts:

```coq
n > 0
0 <= n
0 <= sum
sum + n <= n_pre
0 <= n_pre
```

Even with `0 <= n % 10 <= n`, this proves only `sum + n % 10 <= n_pre`; it does not prove `n_pre <= INT_MAX`. The value `n_pre` is a C `int`, but the generated pure context does not expose that range unless it is recorded in the invariant. This is an annotation-level missing fact, not a Coq tactic issue.

I will strengthen the invariant from:

```c
0 <= n &&
0 <= sum &&
sum + n <= n@pre &&
sum + digit_sum_z(n) == digit_sum_z(n@pre)
```

to:

```c
0 <= n &&
n@pre <= INT_MAX &&
0 <= sum &&
sum + n <= n@pre &&
sum + digit_sum_z(n) == digit_sum_z(n@pre)
```

This does not alter the contract. It preserves a type-range fact for the original integer input so the loop-body addition safety VC can close using `sum + n % 10 <= sum + n <= n@pre <= INT_MAX`.

## Iteration 4: add a bridge assertion while the original `n` local is still available

After adding `n@pre <= INT_MAX` directly to the invariant and regenerating, the initialization obligation became:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| 0 <= n_pre |] && emp
|--
  [| 0 <= n_pre |] &&
  [| n_pre <= INT_MAX |] &&
  ...
```

This is not provable from the contract alone. The missing upper bound comes from the fact that the input parameter is stored in a C `int` local, but the generated pure-only initialization VC has already abstracted away the local memory. The bridge must therefore be placed before the loop invariant, while the current local `n` still equals `n@pre` and the verifier can consume the `Int` local typing information.

I will add this assertion immediately before the invariant:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX
*/
```

The assertion is intentionally small. It only preserves the original-parameter identity and the upper range needed by the loop safety VC. The invariant will then carry `n@pre <= INT_MAX` through the loop.

The first `symexec` attempt with that bridge assertion failed at the loop invariant initialization:

```text
Partial Solve Invariant Error in .../annotated/verify_20260422_154652_digit_sum.c:26:4
Sep cannot be fully solved
The Sep is:
SEP[store(sum_67_addr , sum_76_value , signed int)]
```

The logged left side after the bridge assertion contained only the `n` store:

```text
PROP[ n_pre <= INT_MAX ]
SEP[ store(n_addr, n_pre, signed int) ]
```

Because the assertion did not mention `sum`, the solver did not preserve the `sum` local permission for the immediately following loop invariant. The fix is to include the current accumulator value in the bridge:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX &&
      sum == 0
*/
```

This assertion is still a loop-entry bridge. It records only facts true immediately after initialization and keeps both local stores alive for the loop invariant.

## Retry annotation iteration: remove false upper-bound bridge and bound the live loop state

The current active annotated C contains:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX &&
      sum == 0
*/
/*@ Inv
      0 <= n &&
      n@pre <= INT_MAX &&
      0 <= sum &&
      sum + n <= n@pre &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
```

That bridge assertion generated the current false witness:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  [| (n_pre <= INT_MAX) |] &&
  [| (0 = 0) |] &&
  emp.
```

The assertion `n@pre <= INT_MAX` is not derivable from the formal precondition `0 <= n && emp`, so this retry will stop carrying it as a pure fact. Instead, the loop invariant will carry the direct live-state safety bound needed for the addition:

```c
0 <= n &&
0 <= sum &&
sum + n <= n@pre &&
sum + n <= INT_MAX &&
sum + digit_sum_z(n) == digit_sum_z(n@pre)
```

This change is intentionally small. It preserves the semantic invariant `sum + digit_sum_z(n) == digit_sum_z(n@pre)` and the numeric remaining-state bound `sum + n <= n@pre`, but replaces the false global assertion with the concrete safety fact `sum + n <= INT_MAX`. Initialization should use the local typed `int` state after `int sum = 0`; preservation should use `0 <= n % 10 <= n` and `0 <= n ÷ 10 <= n` under `n > 0`; exit still uses `n <= 0` plus `0 <= n` to reduce to `n == 0`.

## Retry annotation iteration: use the verifier's `by local` int-bound idiom

The current active annotated file `annotated/verify_20260422_154652_digit_sum.c` has this loop invariant:

```c
/*@ Inv
      0 <= n &&
      0 <= sum &&
      sum + n <= n@pre &&
      sum + n <= INT_MAX &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
```

The regenerated loop-entry witness in `coq/generated/digit_sum_goal.v` is:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  ...
  [| ((0 + n_pre ) <= INT_MAX) |] &&
  ...
  emp.
```

So the remaining annotation-side blocker is not the loop arithmetic itself; it is that the invariant directly asks for `0 + n_pre <= INT_MAX` at entry, while the pure `Require` only says `0 <= n_pre`.

The earlier failed bridge assertion was:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX &&
      sum == 0
*/
```

That generated a false pure proof obligation because it asked the assertion solver to prove `n@pre <= INT_MAX` from the contract. The existing example `QualifiedCProgramming/QCP_examples/simple_arith/gcd.c` uses a different annotation form:

```c
/*@ x <= INT_MAX by local*/
```

inside a function whose precondition does not include `x <= INT_MAX`. This indicates that `by local` can derive the C `int` upper bound from the current local variable store instead of from the pure contract.

Planned C change:

```c
int sum = 0;

/*@ n <= INT_MAX by local */

/*@ Inv
      0 <= n &&
      0 <= sum &&
      n@pre <= INT_MAX &&
      sum + n <= n@pre &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
```

This change intentionally removes the invariant entry conjunct `sum + n <= INT_MAX` and replaces it with the more semantic bound `n@pre <= INT_MAX` plus `sum + n <= n@pre`. At loop entry, `sum == 0` and `n == n@pre`, so `sum + n <= n@pre` is immediate, while `n@pre <= INT_MAX` should come from the `by local` extraction while `n` still equals its pre-state value. In the loop body, `sum + n <= n_pre` and `n_pre <= INT_MAX` together provide the upper bound needed for `sum += n % 10`, because for positive `n`, `0 <= n % 10 <= n`.
