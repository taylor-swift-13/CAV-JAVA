# Annotation reasoning

## 2026-04-23 initial loop invariant for `string_count_digits`

Current program point:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 48 && s[i] <= 57) {
        cnt++;
    }
    i++;
}

return cnt;
```

The loop scans a null-terminated `CharArray::full(s, n + 1, app(l, cons(0, nil)))` from left to right. At the loop head, `i` is the number of already processed non-sentinel characters, and `cnt` is intended to equal `string_count_digits_spec` over that processed prefix. With no `Inv`, symexec would have no stable loop summary: after one iteration it must remember the array resource, the bounds needed to read `s[i]`, and the relation between `cnt` and the Coq spec at return.

Planned invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= cnt && cnt <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      cnt == string_count_digits_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization holds with `l1 = nil`, `l2 = l`, `i = 0`, and `cnt = 0`; the spec on `nil` is `0`, and the original char-array resource is unchanged. Preservation follows by using the current nonzero character `s[i]` as the next element of `l2`: the digit branch increments `cnt`, matching the `if 48 <= x <= 57 then 1 else 0` case in `string_count_digits_spec`, while the non-digit branch leaves `cnt` unchanged. The bound `0 <= cnt <= i` is included because each processed character contributes either `0` or `1`, and this gives the integer range facts needed after `cnt++`.

Planned loop-exit assertion:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= cnt && cnt <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      cnt == string_count_digits_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

When `s[i] == 0`, the invariant and the precondition fact that every `l[k]` for `0 <= k < n` is nonzero force `i == n`; otherwise the sentinel read would contradict the nonzero fact for the logical string. With `Zlength(l1) == i` and `l == app(l1, l2)`, `i == n` and `Zlength(l) == n` force `l1 == l` and `l2 == nil`, so `cnt == string_count_digits_spec(l)` is available directly for the postcondition. The assertion is placed immediately after the loop, before `return cnt`, so it fixes the loop exit state while local permissions are still in the standard loop-exit shape.
