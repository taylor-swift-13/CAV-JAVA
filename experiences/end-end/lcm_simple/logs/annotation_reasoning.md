## 2026-04-22 initial LCM loop invariant

Current program point:

```c
int x = a;

while (x % b != 0) {
    x = x + a;
}

return x;
```

The target postcondition is:

```c
lcm_simple_spec(a@pre, b@pre, __return) && emp
```

The loop does not mutate heap memory and does not change `a` or `b`; it only advances local scalar `x` by adding `a`. The proof therefore needs an invariant that keeps `a == a@pre` and `b == b@pre`, tracks that `x` is a positive multiple of `a`, and keeps `x` bounded by the mathematical `lcm_simple_value(a, b)` so the loop body assignment `x = x + a` has an integer-range argument from the contract guard `lcm_simple_value(a, b) <= INT_MAX`.

The annotation to add is:

```c
/*@ Inv exists k,
      1 <= a &&
      1 <= b &&
      a == a@pre &&
      b == b@pre &&
      lcm_simple_value(a, b) <= INT_MAX &&
      1 <= k &&
      x == a * k &&
      x <= lcm_simple_value(a, b)
*/
while (x % b != 0) {
    x = x + a;
}
```

Initialization: immediately after `int x = a`, choose `k = 1`. The precondition gives `1 <= a`, `1 <= b`, and `lcm_simple_value(a, b) <= INT_MAX`; `x == a * 1` and `x <= lcm_simple_value(a, b)` follow from the standard fact that the LCM of two positive integers is a positive multiple of `a`.

Preservation: at the loop head, `x == a * k` and `1 <= k`; the branch condition `x % b != 0` says the current positive multiple of `a` is not yet a common multiple of `a` and `b`. Since `lcm_simple_value(a, b)` is the least positive common multiple and itself a multiple of `a`, the current `k` is strictly below the LCM multiplier, so after `x = x + a` the next value is still `a * (k + 1)` and remains `<= lcm_simple_value(a, b)`. This also provides the C overflow side condition because the LCM bound is at most `INT_MAX`.

Exit usability: when the loop exits, `x % b == 0`. The invariant already gives that `x` is a positive multiple of `a` and `x <= lcm_simple_value(a, b)`. By least-positive-common-multiple reasoning for positive `a` and `b`, `x` must equal `lcm_simple_value(a, b)`, which is exactly the imported postcondition after preserving `a == a@pre` and `b == b@pre`.
