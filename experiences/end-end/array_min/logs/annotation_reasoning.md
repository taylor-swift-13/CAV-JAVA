# Annotation reasoning

## 2026-04-22 initial loop invariant

Current target:

```c
int i;
int ret = a[0];

for (i = 1; i < n; ++i) {
    if (a[i] < ret) {
        ret = a[i];
    }
}

return ret;
```

The contract requires the returned value to be an element of the logical array `l` and to be less than or equal to every `l[i]` for `0 <= i < n`, while preserving `IntArray::full(a, n, l)`. The loop is a prefix scan. At the loop guard, `i` is the next index to inspect, so the already-scanned prefix is `[0, i)`. Before the first guard check, `i == 1` and `ret == a[0]`, and the precondition gives `1 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`, so the scanned prefix is nonempty.

The planned invariant is:

```c
/*@ Inv
      1 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      Zlength(l) == n &&
      (exists idx, 0 <= idx && idx < i && l[idx] == ret) &&
      (forall (j: Z), (0 <= j && j < i) => ret <= l[j]) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) { ... }
```

Initialization: after `ret = a[0]` and `i = 1`, choose `idx = 0`. The array predicate justifies the read of `a[0]` as `l[0]`, and the only element in prefix `[0, 1)` is `l[0]`, so `ret <= l[j]` holds for all prefix indices.

Preservation: assume the invariant and `i < n`. The body reads `a[i]`. If `a[i] < ret`, assigning `ret = a[i]` makes the new witness index `idx = i`; the old prefix elements remain greater than or equal to the old `ret`, and `a[i] < old_ret` implies the new `ret` is also less than or equal to every old prefix element. If the branch is not taken, the old witness index remains valid and the failed comparison gives `ret <= l[i]`, extending the prefix minimum fact to `[0, i + 1)`.

Exit usability: when the loop exits, the invariant gives `i <= n` and the guard failure gives `!(i < n)`, so `i == n`. Substituting `i == n` into the occurrence and lower-bound facts yields exactly the two pure postcondition clauses, and `IntArray::full(a, n, l)` supplies the preserved memory clause.
