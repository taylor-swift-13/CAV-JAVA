## 2026-04-22 lower-bound loop invariant

The active annotated C currently matches `input/binary_search_first.c` and has no `Inv` before:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}

if (left < n && a[left] == target) {
    return left;
}
return -1;
```

This loop is not the ordinary "return any matching index" binary search. It is a lower-bound search over the half-open interval `[left, right)`, with `right` initialized to `n` and the update `right = mid` when `a[mid] >= target`. The postcondition needs the first occurrence: if the function returns `left`, every index `i < left` must have `l[i] != target`; if it returns `-1`, every valid index must differ from `target`.

The needed invariant is therefore a partition invariant:

```c
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      0 <= left && left <= right && right <= n &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      (forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
      (forall (i: Z), (right <= i && i < n) => target <= l[i]) &&
      IntArray::full(a, n, l)
*/
```

Initialization holds because `left == 0` and `right == n`, so both quantified eliminated ranges are empty and the precondition provides sortedness, bounds, and the array resource. Preservation matches the two branches. If `a[mid] < target`, sortedness implies every `i <= mid` is also below `target`, so after `left = mid + 1` the eliminated prefix grows. If `a[mid] >= target`, sortedness implies every `i >= mid` is at least `target`, so after `right = mid` the eliminated suffix grows. The invariant also keeps `a`, `n`, and `target` tied to their pre-state values so the returned `IntArray::full(a, n, l)` and postcondition use the same parameters.

The arithmetic around `mid` is critical for both safety and preservation. Under `left < right` and `0 <= left <= right <= n`, the assignment

```c
mid = left + (right - left) / 2;
```

should establish `left <= mid && mid < right && 0 <= mid && mid < n`; this is needed before reading `a[mid]` and before using sortedness in either branch. I will add a local `Assert` immediately after computing `mid` with exactly these bounds and the invariant facts. This bridge assertion serves the next array read and branch update directly.

At loop exit, `!(left < right)` plus `left <= right` gives `left == right`. The first return branch `left < n && a[left] == target` then uses the prefix fact `(forall i < left, l[i] < target)` to prove the returned index is the first occurrence. The final `return -1` uses the same prefix fact for `i < left`; for `i >= left`, since `left == right`, the suffix fact gives `target <= l[i]`, and the failed equality branch gives `l[left] != target` when `left < n`. Sortedness extends from `left` to later indices. If `left == n`, the prefix covers the whole array. If the generated return witness needs the equality `left == right` explicitly, a loop-exit assertion should be added immediately after the loop, but I will first try the minimal invariant plus the `mid` bridge assertion.
