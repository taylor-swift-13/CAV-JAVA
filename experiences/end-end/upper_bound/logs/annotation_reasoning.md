## 2026-04-23 05:39 +0800 - Add upper-bound loop invariant and midpoint bridge

The active annotated file initially matched the input and had no loop invariant:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] <= target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

This loop is an upper-bound binary search over a sorted array. The final `return left` must prove that every index below the returned value has `l[i] <= target`, and that either the returned value is `n` or the returned array element is strictly greater than `target`. The stable loop state is the half-open active interval `[left,right)`: the discarded prefix `[0,left)` is known to be `<= target`, and the discarded suffix `[right,n)` is known to be `> target`.

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
      (forall (i: Z), (0 <= i && i < left) => l[i] <= target) &&
      (forall (i: Z), (right <= i && i < n) => target < l[i]) &&
      IntArray::full(a, n, l)
*/
```

Initialization holds because `left == 0` and `right == n`, making both quantified discarded regions empty; the contract supplies sortedness, length, integer range, and the full array resource. Preservation follows from sortedness. In the `a[mid] <= target` branch, `left` becomes `mid + 1`, and all newly discarded prefix indices `i <= mid` satisfy `l[i] <= l[mid] <= target`. In the `a[mid] > target` branch, `right` becomes `mid`, and all newly discarded suffix indices `i >= mid` satisfy `target < l[mid] <= l[i]`. At exit, `!(left < right)` and `left <= right` imply `left == right`, so the prefix predicate gives the first postcondition quantifier and the suffix predicate gives `l[left] > target` whenever `left < n`.

The midpoint assignment also needs an assertion before reading `a[mid]`:

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
      (forall (i: Z), (0 <= i && i < left) => l[i] <= target) &&
      (forall (i: Z), (right <= i && i < n) => target < l[i]) &&
      IntArray::full(a, n, l)
*/
```

This bridge exposes that the computed midpoint is a valid array index and remains inside `[left,right)`, while preserving the array resource and the quantified prefix/suffix facts for the two branch-preservation VCs.

## 2026-04-23 05:42 +0800 - Normalize return postcondition comparison in annotated copy

After adding the invariant and midpoint bridge, `symexec` reached:

```text
Symbolic Execution into function upper_bound
End of symbolic execution of function upper_bound
```

but returned nonzero and left `coq/generated/upper_bound_goal_check.v` empty. The diagnostic was:

```text
The array i_94 of Znth is not a list type.
The type is Z
```

The generated `upper_bound_goal.v` was otherwise populated and contained the invariant facts in the intended shape, for example:

```coq
[| forall (i_4: Z),
     (((right <= i_4) /\ (i_4 < n_pre)) ->
       (target_pre < (Znth i_4 l 0))) |]
```

The only remaining source using the opposite comparison orientation was the annotated contract's return disjunct:

```c
(__return < n && l[__return] > target)
```

The front end has already handled the invariant suffix successfully when written as `target < l[i]`, so I am normalizing only the active annotated copy to the semantically equivalent form:

```c
(__return < n && target < l[__return])
```

This does not change the intended postcondition; it avoids the parser/pretty-printer path that malformed the generated `Znth` expression. The formal `input/upper_bound.c` is left unchanged.

## 2026-04-23 05:45 +0800 - Replace scalar return-index postcondition with suffix quantifier

The previous comparison normalization was not sufficient. A clean rerun still failed with the same diagnostic and generated `upper_bound_goal.v` ending at:

```coq
Definition upper_bound_return_wit_1 :=
```

with no body after the definition. This localizes the failure to return VC construction, before `goal_check.v` can be emitted. The invariant and branch VCs before the return are generated normally.

The remaining unstable expression is the scalar postcondition access through `__return`:

```c
((__return == n) ||
 (__return < n && target < l[__return]))
```

For a sorted array, this is equivalent to the suffix property used by the loop invariant:

```c
(forall (i: Z), (__return <= i && i < n) => target < l[i])
```

If `__return == n`, the suffix range is empty. If `__return < n`, the scalar condition at `__return` plus sortedness implies every later element is also greater than `target`; conversely, the suffix quantifier instantiated at `__return` gives the original scalar condition. I am using this equivalent quantified postcondition only in the active annotated copy so the return VC can reuse the invariant's suffix fact directly and avoid the front-end failure on scalar `l[__return]`.
