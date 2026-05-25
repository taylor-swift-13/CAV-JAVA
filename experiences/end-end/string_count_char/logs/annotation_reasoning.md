## Annotation iteration 1

Context: the active annotated file initially has no loop invariant around the `while (1)` scan:

```c
int i = 0;
int ret = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        ret++;
    }
    i++;
}
```

The loop scans the nonzero prefix `l` of `s` from left to right. At the loop head, `i` is the length of the processed prefix and `ret` is the number of occurrences of `c` in that processed prefix. The invariant therefore needs to preserve both the heap resource for the full string and the semantic relation between `ret` and the prefix.

Planned invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= ret && ret <= i &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      ret == string_count_char_spec(l1, c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization: before the first iteration, `i == 0` and `ret == 0`; choose `l1 = nil` and `l2 = l`, so `string_count_char_spec(nil, c) == 0`, `Zlength(l1) == 0`, and the original `CharArray::full` resource is unchanged.

Preservation: if `s[i] == 0`, the loop exits without changing state. Otherwise the contract's nonzero-prefix property and the full string resource imply the current index is still inside `l`; after the optional `ret++`, incrementing `i` extends `l1` by the current character. The relation `ret == string_count_char_spec(l1, c)` follows the same branch as the C code: add one exactly when `s[i] == c`, otherwise leave `ret` unchanged. The bound `0 <= ret && ret <= i` is included so the `ret++` operation has an explicit `INT_MAX` safety path via `i < n` and `n < INT_MAX`.

Exit use: after `break`, `s[i] == 0` plus the precondition that all positions `0 <= k < n` are nonzero should force `i == n`. A loop-exit assertion will expose this and rewrite the processed prefix to the full list for the return witness:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= ret && ret <= n &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      ret == string_count_char_spec(l, c@pre) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion is placed immediately after the loop, before local-variable cleanup at `return`, matching the project guidance for loop-exit assertions.
