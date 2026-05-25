# Annotation Reasoning

## Initial loop invariant and parser helper

Program point: the only loop is `while (n > 0)` in `annotated/verify_20260422_214114_reverse_digits.c`. The active annotated copy currently has no `Inv`, so symbolic execution would have no loop-head summary connecting the mutated quotient `n`, the accumulator `ans`, and the pre-state value `n@pre` used by the postcondition:

```c
Ensure
  __return == reverse_digits_z(n@pre) && emp
```

At the loop head, `ans` is the decimal reversal of the low-order digits already removed from the original input, while current `n` is the remaining high-order quotient. The input Coq file defines this shape through `reverse_digits_acc_fuel n acc fuel`, and `reverse_digits_z n` is `reverse_digits_acc_fuel n 0 (Z.to_nat n)`. Directly writing `Z.to_nat(n)` in a C annotation is not parser-stable in this project; nearby fuelled scalar examples use a workspace-local first-order helper instead. I will add:

```coq
Definition reverse_digits_acc_z (n acc : Z) : Z :=
  reverse_digits_acc_fuel n acc (Z.to_nat n).
```

Then the loop invariant can use this parser-facing symbol:

```c
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      0 <= ans &&
      ans <= reverse_digits_z(n@pre) &&
      reverse_digits_z(n@pre) <= INT_MAX &&
      reverse_digits_acc_z(n, ans) == reverse_digits_z(n@pre)
*/
while (n > 0) {
```

Initialization: after `int ans = 0`, current `n` is still `n@pre`, so `reverse_digits_acc_z(n, 0)` unfolds to `reverse_digits_z(n@pre)`. The lower bound `0 <= n` and final overflow guard come from the function precondition, and the C `int` local store provides the current `n <= INT_MAX` fact.

Preservation: under `n > 0`, the statement `ans = ans * 10 + n % 10` appends the next decimal digit to the accumulator, and `n = n / 10` advances to the quotient. The helper relation should step from `reverse_digits_acc_z(n, ans)` to `reverse_digits_acc_z(n / 10, ans * 10 + n % 10)`. The bound `ans <= reverse_digits_z(n@pre)` is kept because the stepped accumulator is still part of the same final value; concrete arithmetic bounds for multiplication and addition may become manual proof witnesses, but the invariant carries the semantic fact needed to prove them.

Exit usability: after the loop, the invariant and `!(n > 0)` imply `n == 0`. For `n == 0`, `reverse_digits_acc_z(0, ans)` reduces to `ans`, so the invariant gives `ans == reverse_digits_z(n@pre)`. I will add a minimal exit assertion immediately after the loop:

```c
/*@ Assert
      n == 0 &&
      ans == reverse_digits_z(n@pre)
*/
```

This assertion is placed at the true loop exit, before local cleanup, and only bridges the final accumulator relation to the return postcondition.

## Add local representability bridge for `n@pre <= INT_MAX`

The first proof compile attempt reached `proof_of_reverse_digits_entail_wit_1` and showed an annotation-level gap. The generated initialization VC had:

```coq
H  : 0 <= n_pre
H0 : 0 <= reverse_digits_z n_pre
H1 : reverse_digits_z n_pre <= 2147483647
============================
n_pre <= 2147483647
```

The invariant includes `n <= INT_MAX`, which is true because function parameter `n` is stored as a C `int`, but that representability fact was not present in the pure precondition after the invariant initialization VC was generated. This is the exact pattern documented in `ASSERTION.md` section 8: extract the C `int` range fact with a local-store assertion while the local variable is still in scope.

I will insert the bridge immediately after `ans = 0` and before the loop invariant:

```c
/*@ n <= INT_MAX by local */
```

This does not change the formal input contract. It only lets symbolic execution carry the local `int` upper bound into the invariant initialization proof. After this annotation edit, I must rerun `symexec` and use the freshly generated witness list.
