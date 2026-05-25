## 2026-04-22 annotation round 1: add prefix-update loop invariant

Program point: the only loop in `array_increment`, immediately before `for (i = 0; i < n; ++i)`.

Current unannotated loop:

```c
for (i = 0; i < n; ++i) {
    a[i] = a[i] + 1;
}
```

The function owns `IntArray::full(a, n, l)` on entry and must return some `lr` such that every index in `[0, n)` satisfies `lr[i] == l[i] + 1`. The loop variable `i` is the next index to update, so at the loop guard the prefix `[0, i)` has already been incremented and the suffix `[i, n)` still has the original value from `l`.

Planned invariant:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == l[k] + 1) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == l[k]) &&
      IntArray::full(a, n@pre, lr)
*/
```

Initialization: after `i = 0`, choose `lr = l`. The processed-prefix condition is vacuous because there is no `k` with `0 <= k < 0`; the suffix condition says every index in `[0, n)` still equals `l[k]`, which follows from the initial `IntArray::full(a, n, l)` and `Zlength(l) == n`.

Preservation: inside the body, the loop guard provides `0 <= i && i < n@pre`. Before the write, a bridge assertion exposes the focused cell from `IntArray::full(a, n@pre, lr)`:

```c
IntArray::missing_i(a, i, 0, n@pre, lr) *
data_at(a + (i * sizeof(int)), int, l[i])
```

The value is `l[i]` because the suffix part of the invariant includes index `i`. The contract's overflow guard applies at this same index, so `a[i] + 1` is an in-range signed int. After the assignment, the focused cell contains `l[i] + 1`. A second bridge assertion restores a full array with witness `lr'`, whose prefix through `i` satisfies `lr'[k] == l[k] + 1` and whose suffix after `i` still satisfies `lr'[k] == l[k]`.

Planned post-write bridge:

```c
/*@ exists lr,
      ...
      IntArray::missing_i(a, i, 0, n@pre, lr) *
      data_at(a + (i * sizeof(int)), int, l[i] + 1)
    which implies
      exists lr',
        Zlength(lr') == n@pre &&
        (forall (k: Z), (0 <= k && k < i + 1) => lr'[k] == l[k] + 1) &&
        (forall (k: Z), (i + 1 <= k && k < n@pre) => lr'[k] == l[k]) &&
        IntArray::full(a, n@pre, lr')
*/
```

Exit usability: when the loop exits, the invariant gives `i <= n@pre`; the failed guard gives `!(i < n@pre)`, so `i == n@pre`. The prefix condition then covers every index in `[0, n)`, which is exactly the existential array relation required by the postcondition. No separate loop-exit assertion should be necessary unless `symexec` reports a return witness gap.
