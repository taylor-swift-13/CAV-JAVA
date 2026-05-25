## 2026-04-22 18:56 +0800 - Add lower-bound loop invariant and midpoint bridge

The active annotated file initially matched the input and had no loop invariant:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

This is a lower-bound binary search over a sorted array. The postcondition after `return left` needs two global facts: every index below the returned value is strictly below `target`, and every index from the returned value to `n - 1` is at least `target`. Therefore the loop invariant should describe the already-discarded prefix `[0,left)` and suffix `[right,n)`, not just numeric bounds on `left` and `right`.

The invariant to add immediately before the `while` is:

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

Initialization holds because `left == 0` and `right == n`, so both quantified regions are empty, and the input contract already supplies sortedness, length, integer bounds, and `IntArray::full(a,n,l)`. Preservation holds by sortedness. In the `a[mid] < target` branch, `left` becomes `mid + 1`; all newly consumed indices `i <= mid` are below `target` because `l[i] <= l[mid] < target`. In the other branch, `right` becomes `mid`; all newly consumed suffix indices `i >= mid` satisfy `target <= l[i]` because `target <= l[mid] <= l[i]`. Exit is directly useful: `!(left < right)` plus `left <= right` gives `left == right`, so the invariant's prefix and suffix facts are exactly the two quantified postcondition clauses.

The midpoint assignment also needs a bridge assertion before `a[mid]` is read:

```c
/*@ Assert
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      0 <= left && left < right && right <= n &&
      0 <= mid && mid < n &&
      left <= mid && mid < right &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      (forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
      (forall (i: Z), (right <= i && i < n) => target <= l[i]) &&
      IntArray::full(a, n, l)
*/
```

This assertion exposes the arithmetic consequences of `left < right` and `mid = left + (right - left) / 2`: `mid` is a valid array index, remains in `[left,right)`, and the same resource and quantified facts are still available for the branch update VCs.
