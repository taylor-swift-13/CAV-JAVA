## 2026-04-23 Annotation iteration 1

Current program point: the `while (1)` string scan in `string_count_lowercase` has no `Inv`, so symbolic execution would have no stable loop state for the scan index `i`, accumulator `cnt`, or preserved `CharArray::full` resource.

Relevant unannotated C fragment:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 97 && s[i] <= 122) {
        cnt++;
    }
    i++;
}

return cnt;
```

Planned invariant mirrors the existing `string_count_digits` and `string_count_char` examples. It splits the logical input list as `l == app(l1, l2)`, records `Zlength(l1) == i`, keeps the heap as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, and makes the accumulator exact: `cnt == string_count_lowercase_spec(l1)`. It also preserves `s == s@pre`, `0 <= i && i <= n`, and `0 <= cnt && cnt <= i`; the latter gives the `cnt++` overflow check because the loop body executes only when `i < n` and the precondition has `n < INT_MAX`.

The loop-exit assertion should be placed immediately after the loop, while local variables are still available. On the break path, the invariant and the string terminator read establish `i == n` because all positions `0 <= k < n` are nonzero and the char array stores the unique terminator at index `n`. With `Zlength(l1) == n`, `Zlength(l) == n`, and `l == app(l1, l2)`, the assertion records the intended post-loop fact `cnt == string_count_lowercase_spec(l)`. This is a small exit bridge rather than a replacement for the invariant.

Annotation to insert:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= cnt && cnt <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      cnt == string_count_lowercase_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Exit assertion to insert:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= cnt && cnt <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      cnt == string_count_lowercase_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```
