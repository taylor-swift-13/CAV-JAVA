## 2026-04-23 01:16:15 +0800 - Initial loop invariant for string_count_spaces

Current annotated code has no loop invariant:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == 32) {
        cnt++;
    }
    i++;
}

return cnt;
```

The function scans a null-terminated character array whose logical contents are `app(l, cons(0, nil))`. The loop variable `i` is the length of the processed prefix, and `cnt` must be the count of ASCII spaces in that processed prefix. The postcondition requires `cnt == string_count_spaces_spec(l)` at return and preservation of `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.

The planned invariant follows the same shape as the completed local `string_count_digits` example, specialized from digit classification to `x == 32`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= cnt && cnt <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      cnt == string_count_spaces_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization should hold with `i == 0`, `cnt == 0`, `l1 == nil`, and `l2 == l`; `string_count_spaces_spec(nil) == 0`, and the original heap resource is unchanged. For preservation, when `s[i] != 0`, the contract's nonzero-prefix fact and `i < n` identify the current character as the next element of `l2`; after the optional increment and `i++`, the processed prefix becomes the old `l1` plus that one element, matching the recursive definition of `string_count_spaces_spec`. The bound `cnt <= i` is preserved because a count over a prefix can increase by at most one per processed character.

The loop exits only through `if (s[i] == 0) break;`. With the invariant and the contract fact that all positions `0 <= k < n` in `l` are nonzero, reading zero at position `i` should force `i == n`. A loop-exit assertion immediately after the loop will pin down `i == n`, `cnt == string_count_spaces_spec(l)`, and the preserved array resource for the return witness:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= cnt && cnt <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      cnt == string_count_spaces_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion is placed before `return cnt`, while local permissions for `i` and `cnt` are still present, matching the local pattern from `string_count_digits` and avoiding a late assertion after locals are cleaned up.
