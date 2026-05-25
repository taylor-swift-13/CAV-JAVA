## 2026-04-22 09:15:12 +0800 - binary_search loop invariant design

Current annotated file `annotated/verify_20260422_091409_binary_search.c` has a `while (left <= right)` loop with no `Inv`, so symbolic execution cannot know which part of the sorted array has already been ruled out when the loop exits and returns `-1`.

Relevant current C fragment:

```c
int left = 0;
int right = n - 1;
int mid;

while (left <= right) {
    mid = left + (right - left) / 2;
    if (a[mid] == target) {
        return mid;
    }
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid - 1;
    }
}

return -1;
```

The loop state is a shrinking closed interval `[left, right]`. Values at indices strictly before `left` have already been eliminated because sortedness and a previous comparison showed they are less than `target`; values strictly after `right` have already been eliminated because sortedness and a previous comparison showed they are greater than `target`.

Planned invariant:

```c
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      0 <= left && left <= n &&
      -1 <= right && right < n &&
      left <= right + 1 &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      (forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
      (forall (i: Z), (right < i && i < n) => target < l[i]) &&
      IntArray::full(a, n, l)
*/
while (left <= right) { ... }
```

Initialization holds because `left == 0` makes the eliminated-left quantified range empty, and `right == n - 1` makes the eliminated-right quantified range empty. The bounds also cover the `n == 0` case: `right == -1`, `left == 0`, and `left <= right + 1`.

For preservation in the `a[mid] < target` branch, `left` becomes `mid + 1`. Every newly eliminated index `i <= mid` satisfies `l[i] <= l[mid] < target` by sortedness, so the eliminated-left fact remains true. For preservation in the `else` branch after `a[mid] != target` and not `a[mid] < target`, the comparison facts imply `target < l[mid]`; every newly eliminated index `i >= mid` satisfies `l[mid] <= l[i]`, so the eliminated-right fact remains true.

The loop exit condition is `left > right`. Together with invariant `left <= right + 1`, this gives `left == right + 1`. Thus every valid index is either `i < left` or `right < i`, so the two eliminated-range facts imply `l[i] != target` for all `0 <= i < n`. I will add a loop-exit `Assert` directly after the loop with this exact post-loop state, following `ASSERTION.md` guidance to keep it close to the exit point.

## 2026-04-22 09:16:22 +0800 - Bridge assertion for `a[mid]` read

After adding the initial invariant and exit assertion, the clean `symexec` run parsed the file but failed before VC generation at the first array read:

```text
fatal error: Cannot derive the precondition of Memory Read. in .../annotated/verify_20260422_091409_binary_search.c:44:8
```

The failing program point is:

```c
while (left <= right) {
    mid = left + (right - left) / 2;
    if (a[mid] == target) {
        return mid;
    }
```

The invariant plus loop guard imply `0 <= left <= right < n`. The assignment computes `mid = left + (right - left) / 2`, so mathematically `left <= mid <= right`, hence `0 <= mid && mid < n`. The symbolic executor is not deriving this division/bounds fact strongly enough to open `IntArray::full(a, n, l)` for `a[mid]`.

I will add a bridge assertion immediately after the assignment and immediately before the first memory read:

```c
/*@ Assert
      0 <= mid && mid < n &&
      left <= mid && mid <= right &&
      IntArray::full(a, n, l)
*/
```

This assertion is intentionally local: it only exposes the index bounds and heap shape needed by the next statement, without changing the loop invariant or trying to encode later return reasoning.

## 2026-04-22 09:16:57 +0800 - Preserve full state across the `mid` bridge assertion

The previous bridge assertion was too narrow. The next `symexec` run failed at the second comparison:

```text
fatal error: cannot find the program variable target(82) in assertion, please check the @pre or related which implies in .../annotated/verify_20260422_091409_binary_search.c:49:8
```

The relevant code was:

```c
mid = left + (right - left) / 2;
/*@ Assert
      0 <= mid && mid < n &&
      left <= mid && mid <= right &&
      IntArray::full(a, n, l)
*/
if (a[mid] == target) {
    return mid;
}
if (a[mid] < target) {
    left = mid + 1;
}
```

This shows that `Assert` acts as a cut: facts and live variable permissions not repeated in the assertion are not available afterward. The bridge must therefore preserve the full loop context, not only the local index bound. I will replace it with an assertion that keeps the same pure facts as the invariant, the eliminated-range facts, unchanged-parameter facts, and `IntArray::full(a, n, l)`, while adding `0 <= mid && mid < n` and `left <= mid && mid <= right`.

The planned assertion shape is:

```c
/*@ Assert
      0 <= n && n <= INT_MAX && Zlength(l) == n &&
      sortedness(l, n) &&
      0 <= left && left <= n &&
      -1 <= right && right < n &&
      left <= right + 1 &&
      0 <= mid && mid < n &&
      left <= mid && mid <= right &&
      a == a@pre && n == n@pre && target == target@pre &&
      eliminated-left facts &&
      eliminated-right facts &&
      IntArray::full(a, n, l)
*/
```

This should keep both array-read preconditions and subsequent comparison variables available.

## 2026-04-22 09:17:32 +0800 - Remove loop-exit assertion that drops `mid` local permission

After widening the `mid` bridge assertion, `symexec` progressed through the loop but failed at the function exit:

```text
fatal error: Error: Fail to Remove Memory Permission of mid:106 in .../annotated/verify_20260422_091409_binary_search.c:85:4
Address found : null
```

The failure points to the post-loop assertion before `return -1`:

```c
/*@ Assert
      left == right + 1 &&
      ...
      (forall (i: Z), (0 <= i && i < n) => l[i] != target) &&
      IntArray::full(a, n, l)
*/
return -1;
```

This assertion is too late and too strong as a cut: it omits the local variable `mid`, but `mid` was declared before the loop and may be uninitialized if the loop is skipped, for example when `n == 0`. This matches the `ASSERTION.md` warning that loop-exit assertions can trigger local permission cleanup failures if placed too late.

I will remove the post-loop `Assert` entirely. The loop invariant already records the eliminated-left and eliminated-right semantic facts, and the negated loop condition provides `left > right`; together with invariant `left <= right + 1`, this is enough for the generated return witness/proof layer to prove the final `forall i, l[i] != target` fact without cutting away `mid`.
