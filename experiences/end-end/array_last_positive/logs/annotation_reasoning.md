# Annotation reasoning

## 2026-04-22 prefix-last-positive invariant for `array_last_positive`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_last_positive`. The implementation is read-only with respect to the input array: it initializes `ans = -1`, scans `a[0..n)`, and assigns `ans = i` whenever the current element is positive. The postcondition requires either `__return == -1` with every array element nonpositive, or a returned index whose element is positive and every later element is nonpositive.

Current annotated C has no loop invariant:

```c
int i;
int ans = -1;

for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        ans = i;
    }
}

return ans;
```

This is too weak for symbolic execution because the final return witness needs the accumulated "last positive so far" fact. The loop-test state should summarize the processed prefix `[0, i)`: either no processed element is positive, represented by `ans == -1`, or `ans` is a valid processed prefix index where `l[ans] > 0` and every later processed prefix index is nonpositive.

Planned loop invariant uses guarded implications rather than a top-level disjunction, following the nearby verified `array_find_last_equal` pattern:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      -1 <= ans && ans < i &&
      Zlength(l) == n &&
      (ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] <= 0)) &&
      (0 <= ans => (l[ans] > 0 &&
                    (forall (j: Z), (ans < j && j < i) => l[j] <= 0))) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

Initialization: after `ans = -1` and `i = 0`, `0 <= i && i <= n` follows from `0 <= n`; `-1 <= ans && ans < i` is `-1 <= -1 && -1 < 0`; and the `ans == -1` implication only asks for a vacuous fact over the empty range `0 <= j < 0`. The array resource, `a == a@pre`, `n == n@pre`, and `Zlength(l) == n` are unchanged from the precondition.

Preservation: in the loop body, `i < n` makes `a[i]` a valid read. If `a[i] > 0`, assigning `ans = i` establishes the nonnegative-`ans` implication for the next prefix `[0, i + 1)`: `l[i] > 0` comes from the branch condition, and there is no `j` satisfying `i < j < i + 1`. If `a[i] <= 0`, the old active implication is extended to `[0, i + 1)` using the failed branch condition for the new endpoint.

Exit usability: when the loop exits, the loop condition gives `i >= n` and the invariant gives `i <= n`, so `i == n`. A minimal loop-exit assertion should expose the invariant specialized from processed prefix `[0, i)` to the full array `[0, n)` immediately before `return ans`:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      -1 <= ans && ans < n &&
      Zlength(l) == n &&
      (ans == -1 => (forall (j: Z), (0 <= j && j < n) => l[j] <= 0)) &&
      (0 <= ans => (l[ans] > 0 &&
                    (forall (j: Z), (ans < j && j < n) => l[j] <= 0))) &&
      IntArray::full(a, n, l)
*/
return ans;
```

This assertion is placed directly after loop exit, before local-variable cleanup. It is still a single assertion shape, so it avoids the assertion-count mismatch that can occur when a loop invariant contains a top-level `||`.
