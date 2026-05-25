## 2026-04-23 01:25:11 +0800 - Add prefix-count loop invariant

Current annotated file is still identical to `input/string_count_vowels.c`; the loop has no `Inv`, so `symexec` would not have a stable assertion at the `while (1)` head for the scanned prefix, accumulator value, preserved string memory, and exit-to-postcondition relationship.

Relevant unannotated C fragment:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
        s[i] == 111 || s[i] == 117) {
        cnt++;
    }
    i++;
}

return cnt;
```

The loop is a single-pass string scan. At the loop head, `i` is the number of processed nonzero characters and the next read position. The accumulator `cnt` should equal `string_count_vowels_spec(l1)` for the processed prefix `l1`, where the original input list is split as `l == app(l1, l2)` and `Zlength(l1) == i`. The memory predicate must continue to own the whole null-terminated string `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, because the function only reads from `s` and the postcondition must return the same full array.

Planned invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= cnt && cnt <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      cnt == string_count_vowels_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization holds with `i == 0`, `cnt == 0`, `l1 == nil`, and `l2 == l`; the spec on `nil` is `0`. Preservation holds because a nonzero read at `s[i]` consumes one element from `l2`, updates `cnt` exactly when that element is one of the five vowel codes, and increments `i`, so the processed prefix summary remains aligned with the recursive spec. The null-character branch exits only at position `i`; combined with the precondition that every index `< n` in `l` is nonzero and the full array has terminator at index `n`, this should force `i == n`.

Planned loop-exit assertion:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= cnt && cnt <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      cnt == string_count_vowels_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion is placed immediately after the loop, while local variables and the string resource are still available. It records the minimal exit facts needed by `return cnt`: the whole list has been processed (`i == n`, `Zlength(l1) == n`, and `l == app(l1, l2)`), the accumulator equals `string_count_vowels_spec(l)`, and the original `CharArray::full` resource is still present.
