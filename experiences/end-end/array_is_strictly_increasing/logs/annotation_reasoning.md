# Annotation reasoning

## 2026-04-22 05:29 - prefix invariant for adjacent strict increase scan

Current annotated code has no loop invariant:

```c
int i;

for (i = 1; i < n; ++i) {
    if (a[i - 1] >= a[i]) {
        return 0;
    }
}

return 1;
```

The contract requires a read-only array predicate to be preserved and a return value that distinguishes two cases:

```c
Ensure
  ((__return == 1 &&
    (forall (i: Z), (1 <= i && i < n) => l[i - 1] < l[i])) ||
   (__return == 0 &&
    (exists i, 1 <= i && i < n && l[i - 1] >= l[i]))) &&
  IntArray::full(a, n, l)
```

The loop scans adjacent pairs. At the loop test before an iteration with index `i`, every adjacent pair ending before `i` has already been checked and found strictly increasing. The loop starts with `i = 1`; because the precondition allows `n == 0`, the invariant cannot require `i <= n`. Following `INV.md` rule 14, the boundary must be valid immediately after the `for` initializer and before checking `i < n`, so the stable bound is `1 <= i && i <= n@pre + 1`.

Planned invariant:

```c
/*@ Inv
      1 <= i && i <= n@pre + 1 &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (1 <= j && j < i) => l[j - 1] < l[j]) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 1; i < n; ++i) {
```

Initialization: after `i = 1`, the quantified range `1 <= j && j < 1` is empty, and `1 <= 1 <= n + 1` follows from `0 <= n`.

Preservation: inside the body, the loop guard gives `i < n`, so both `a[i - 1]` and `a[i]` are in bounds. If the branch `a[i - 1] >= a[i]` is taken, returning `0` can use witness `i` for the existential failure condition. If the branch is not taken, then `l[i - 1] < l[i]`; after `++i`, the quantified prefix extends exactly by this one adjacent pair.

Exit: when the loop exits normally, the invariant says every pair with endpoint `< i` is strictly increasing, and the failed guard gives `i >= n`. Therefore every `j` with `1 <= j && j < n` also has `j < i`, which matches the `__return == 1` postcondition. The array is never modified, and the invariant carries `IntArray::full(a, n@pre, l)` plus parameter equalities back to the postcondition shape.
