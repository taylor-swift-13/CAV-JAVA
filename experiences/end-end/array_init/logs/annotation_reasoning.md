## 2026-04-22 annotation round 1: add prefix-zero loop invariant

Program point: the only loop in `array_init`, immediately before `for (i = 0; i < n; ++i)`.

Current annotated source before this edit:

```c
int i;

for (i = 0; i < n; ++i) {
    a[i] = 0;
}
```

The function owns `IntArray::full(a, n, l)` on entry and must return an existential list `lr` of length `n` where every valid element is zero. The loop variable `i` is the next index to write. At the loop guard, the semantic split is: prefix `[0, i)` has already been overwritten with `0`, and suffix `[i, n)` still contains the original values from `l`.

Planned invariant:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == 0) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == l[k]) &&
      IntArray::full(a, n@pre, lr)
*/
```

Initialization: after `i = 0`, choose `lr = l`. The processed-prefix condition is vacuous because no `k` satisfies `0 <= k < 0`; the suffix condition covers all indices `[0, n)` and follows from the original array contents. The bounds use `0 <= n` from the precondition, and `n@pre == Zlength(l)` records the stable length fact needed by later witnesses.

Preservation: inside the loop, the guard gives `0 <= i && i < n@pre`. Before `a[i] = 0`, a bridge assertion exposes the focused cell from `IntArray::full(a, n@pre, lr)`:

```c
IntArray::missing_i(a, i, 0, n@pre, lr) *
data_at(a + (i * sizeof(int)), int, l[i])
```

The focused value is `l[i]` because the suffix condition applies at the current index `i`. After the assignment, the focused cell contains `0`. A second bridge assertion restores a full array with witness `lr'`, whose prefix through `i` is zero and whose suffix after `i` still equals `l`.

Planned post-write bridge:

```c
/*@ exists lr,
      ...
      IntArray::missing_i(a, i, 0, n@pre, lr) *
      data_at(a + (i * sizeof(int)), int, 0)
    which implies
      exists lr',
        Zlength(lr') == n@pre &&
        (forall (k: Z), (0 <= k && k < i + 1) => lr'[k] == 0) &&
        (forall (k: Z), (i + 1 <= k && k < n@pre) => lr'[k] == l[k]) &&
        IntArray::full(a, n@pre, lr')
*/
```

Exit usability: when the loop exits, the invariant gives `i <= n@pre`; the failed guard gives `!(i < n@pre)`, so `i == n@pre`. The prefix condition then covers every valid index in `[0, n)`, exactly matching the postcondition's universal zero property. No loop-exit assertion is planned for the first run because the invariant already contains the postcondition-facing existential `lr`.
