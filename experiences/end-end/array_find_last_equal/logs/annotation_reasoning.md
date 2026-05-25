# Annotation reasoning

## 2026-04-22 prefix-last-match invariant for `array_find_last_equal`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_find_last_equal`. The implementation is read-only with respect to the input array: it initializes `ans = -1`, scans `a[0..n)`, and assigns `ans = i` whenever the current element equals `k`. The postcondition requires either `__return == -1` with no matching element anywhere in `l[0..n)`, or a returned index that contains `k` and has no later matching element to its right.

Current annotated C has no loop invariant:

```c
int i;
int ans = -1;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        ans = i;
    }
}

return ans;
```

This is too weak for symbolic execution because the final return witness needs the accumulated "last match so far" fact. The key state at the loop test is over the processed prefix `[0, i)`: either no processed element equals `k`, represented by `ans == -1`, or `ans` is a valid processed prefix index where `l[ans] == k` and every later processed prefix index is different from `k`.

Planned loop invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      -1 <= ans && ans < i &&
      Zlength(l) == n &&
      ((ans == -1 &&
        (forall (j: Z), (0 <= j && j < i) => l[j] != k)) ||
       (0 <= ans && ans < i &&
        l[ans] == k &&
        (forall (j: Z), (ans < j && j < i) => l[j] != k))) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

Initialization: after `ans = -1` and `i = 0`, the bounds `0 <= i && i <= n` follow from `0 <= n`, `-1 <= ans && ans < i` is `-1 <= -1 && -1 < 0`, and the no-match branch is vacuous because no `j` satisfies `0 <= j < 0`. The array resource and the parameter equalities are unchanged.

Preservation: at the loop body, `i < n` makes `a[i]` a valid read. If `a[i] == k`, the assignment `ans = i` makes the new `ans` the last match in the prefix `[0, i + 1)`, because there is no index strictly between old `i` and new `i + 1`. If `a[i] != k`, the existing branch is preserved and extended: in the `ans == -1` case, the failed comparison extends the no-match property to `[0, i + 1)`; in the `ans >= 0` case, it extends the "no later match after ans" property to `[ans + 1, i + 1)`.

Exit usability: when the loop exits, `i >= n` with invariant `i <= n` gives `i == n`. The invariant then becomes exactly the return postcondition for `ans`, after replacing the processed-prefix upper bound `i` with `n`. A minimal loop-exit assertion should expose that shape before local variables are cleaned up:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      -1 <= ans && ans < n &&
      Zlength(l) == n &&
      ((ans == -1 &&
        (forall (j: Z), (0 <= j && j < n) => l[j] != k)) ||
       (0 <= ans && ans < n &&
        l[ans] == k &&
        (forall (j: Z), (ans < j && j < n) => l[j] != k))) &&
      IntArray::full(a, n, l)
*/
return ans;
```

The assertion is placed immediately after loop exit and immediately before `return ans`, matching the `array_contains` pattern in `examples/array_contains/annotated/array_contains.c`.

## 2026-04-22 rewrite disjunctive invariant as implications after `symexec` assertion-count failure

Observed failure: rerunning `symexec` on `annotated/verify_20260422_040059_array_find_last_equal.c` failed at the loop invariant control point with:

```text
fatal error: The number of now assertions and loop inv pre assertions does not match. in .../annotated/verify_20260422_040059_array_find_last_equal.c:37:4
```

The failing invariant used an explicit top-level disjunction to model the two cases for `ans`:

```c
((ans == -1 &&
  (forall (j: Z), (0 <= j && j < i) => l[j] != k)) ||
 (0 <= ans && ans < i &&
  l[ans] == k &&
  (forall (j: Z), (ans < j && j < i) => l[j] != k)))
```

This is semantically right, but the frontend appears to split it into multiple assertion cases at the loop invariant boundary, while the current symbolic state before the invariant is a single assertion. That shape mismatch is a symbolic-execution annotation issue, not a Coq proof issue.

Planned replacement: keep a single assertion by using implications guarded by `ans == -1` and `0 <= ans`, with `-1 <= ans && ans < i` providing the coarse range. The invariant becomes:

```c
-1 <= ans && ans < i &&
(ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] != k)) &&
(0 <= ans => (l[ans] == k &&
              (forall (j: Z), (ans < j && j < i) => l[j] != k))) &&
IntArray::full(a, n, l)
```

Initialization is unchanged: `ans == -1`, so the first implication requires only the vacuous empty-prefix fact, and the second implication has a false guard. Preservation is unchanged: assignment `ans = i` establishes the nonnegative implication for the next prefix, while the no-assignment branch extends whichever implication was active using the failed comparison. Exit usability still gives the original postcondition by splitting on the integer fact `-1 <= ans`: either `ans == -1` or `0 <= ans`.

The loop-exit assertion is rewritten in the same single-assertion implication shape so `return ans` receives the same facts over `[0, n)`.
