## 2026-04-23 02:34 Annotation iteration 1

Current program point: the only loop is

```c
for (i = 0; i < n; ++i) {
    s[i] = c;
}
s[n] = 0;
```

The input contract owns `CharArray::full(s, n + 1, l)` with `Zlength(l) == n + 1`. The postcondition needs an output list `lr` of the same length where every index `0 <= i < n` equals `c`, index `n` equals `0`, and the same full char-array resource is returned. Without an invariant, symbolic execution has no stable logical list describing the partially updated buffer after each loop iteration.

The loop variable `i` denotes the number of prefix positions already overwritten. At the `for` invariant control point, before checking `i < n`, the correct state is:

```c
exists lr,
  0 <= i && i <= n@pre &&
  s == s@pre &&
  n == n@pre &&
  c == c@pre &&
  Zlength(lr) == n@pre + 1 &&
  (forall (k: Z), (0 <= k && k < i) => lr[k] == c) &&
  (forall (k: Z), (i <= k && k < n@pre + 1) => lr[k] == l[k]) &&
  CharArray::full(s, n@pre + 1, lr)
```

Why this should initialize: after `i = 0`, the processed-prefix condition is vacuous, the unprocessed suffix condition covers all indices `0 <= k < n + 1`, and the initial heap is exactly `CharArray::full(s, n + 1, l)`, so choosing `lr = l` satisfies the invariant.

Why this should be preserved: inside a loop body, `0 <= i < n@pre`; writing `s[i] = c` changes exactly the current unprocessed cell. The next invariant instance should choose the list obtained by replacing index `i` with `c`. Its processed prefix grows from `[0, i)` to `[0, i + 1)`, while the suffix `[i + 1, n + 1)` remains equal to the original `l`.

Why this helps at loop exit: when the loop exits, `i >= n@pre` and the invariant has `i <= n@pre`, so `i == n@pre`. The prefix property then gives every index `< n` equals `c`, and the suffix property still gives the terminator slot `lr[n] == l[n]` before the final assignment. The subsequent `s[n] = 0` can update that final cell and produce the postcondition witness with prefix `c` and final zero.

