# Annotation Reasoning

## 2026-04-22 06:22:55 +0800 - Add prefix/suffix invariant for `array_negate`

- Program point: the only loop is `for (i = 0; i < n; ++i)` in `annotated/verify_20260422_062136_array_negate.c`.
- Current annotated state before editing:

```c
int i;

for (i = 0; i < n; ++i) {
    out[i] = -a[i];
}
```

- Current issue before editing: the active annotated copy has no loop invariant. The loop progressively writes `out[0..i)` while preserving `a`, so `symexec` has no stable loop-head summary that both preserves the input heap and records the already-written output prefix needed by the postcondition:

```c
Ensure
  exists lr,
    Zlength(lr) == n &&
    (forall (i: Z), (0 <= i && i < n) => lr[i] == -la[i]) &&
    IntArray::full(a, n, la) *
    IntArray::full(out, n, lr)
```

- Planned annotation: add an invariant immediately before the `for` loop with two existential lists:
  - `l1` is the already-written prefix of `out`, with `Zlength(l1) == i` and every `l1[t] == -la[t]` for `0 <= t < i`.
  - `l2` is the untouched suffix copied from the original output list `lo`, with `Zlength(l2) == n@pre - i` and every `l2[t] == lo[i + t]`.
  - The heap shape is `IntArray::full(a, n@pre, la) * IntArray::full(out, n@pre, app(l1, l2))`.

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] == -la[t]) &&
      (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
for (i = 0; i < n; ++i) {
    out[i] = -a[i];
}
```

- Why initialization should hold: after `i = 0`, choose `l1` as the empty prefix and `l2` as `lo`. The original precondition gives `Zlength(lo) == n`, `IntArray::full(a, n, la)`, and `IntArray::full(out, n, lo)`, which matches `app(l1, l2)` at the loop head. The bound `0 <= i && i <= n@pre` follows from `i == 0` and `0 <= n`.
- Why preservation should hold: when `i < n`, the invariant gives `a[i] == la[i]` and `out` as a full array whose `i`-th element lies at the first position of the suffix. The contract overflow guard gives `-2147483648 <= -la[i] <= 2147483647`, so `out[i] = -a[i]` is a valid int write. After the write, the new prefix is the old `l1` extended with `-la[i]`, and the suffix is `sublist(i + 1, n@pre, lo)`, so the same invariant should hold at the next loop head.
- Why exit should prove the postcondition: when the loop exits, `i == n@pre`; the suffix length is `0`, and `IntArray::full(out, n@pre, app(l1, l2))` reduces to a full output list whose whole range satisfies `lr[k] == -la[k]`. The invariant also preserves `a == a@pre`, `out == out@pre`, `n == n@pre`, and `IntArray::full(a, n@pre, la)`, so the function postcondition can use `lr = app(l1, l2)`.
- No extra `Assert` or `which implies` is planned for the first attempt. If `symexec` reports a concrete bridge failure around the array read/write, the next iteration should add the smallest bridge at that statement and rerun symbolic execution.
