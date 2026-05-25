## Annotation iteration 1

Current annotated C has no loop invariant:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] < 48 || s[i] > 57) {
        return 0;
    }
    i++;
}
```

The loop scans the null-terminated buffer `s` from left to right. At the loop head, `i` is the number of characters already accepted as digits, and the next read is `s[i]`. The postcondition needs the whole original buffer unchanged and a return value equal to `string_all_digits_spec(l)`. Therefore the invariant must preserve the full `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, the pointer identity `s == s@pre`, the original nonzero-before-terminator fact, and enough semantic information about the processed prefix.

The planned invariant is:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_all_digits_spec(l1) == 1 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization holds with `l1 = nil`, `l2 = l`, and `i = 0`; `string_all_digits_spec(nil) == 1` by simplification. Preservation after the two digit checks holds because the current character is in range `48..57`, so appending it to `l1` preserves `string_all_digits_spec(l1) == 1`, while the buffer resource is read-only. The early `return 0` branches use the invariant plus the current bad character to show `string_all_digits_spec(l) == 0`. The break branch uses `s[i] == 0` plus the precondition that all `l[k]` for `k < n` are nonzero to force `i == n`; then `l2` is empty and `string_all_digits_spec(l) == 1`, matching the final `return 1`.
