## 2026-04-23 annotation iteration 1

Current program point:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    i++;
}

return i;
```

The loop scans the owned null-terminated `CharArray::full(s, n + 1, app(l, cons(0, nil)))` without modifying it.  The postcondition needs `__return == n` and the same full array resource.  At the loop head, `i` is the number of already inspected nonzero characters and also the next index to read.  The invariant must preserve the array resource, the original pointer relation needed by the postcondition, the length fact `Zlength(l) == n`, and the contract fact that every payload index `0 <= k < n` is nonzero.

Planned invariant:

```c
/*@ Inv Assert
      0 <= i && i <= n &&
      n < INT_MAX &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization holds because the precondition gives `0 <= n`, `n < INT_MAX`, `Zlength(l) == n`, the nonzero payload fact, and the full array resource; after `int i = 0`, `0 <= i && i <= n` follows from `0 <= n`.  Preservation holds on the non-break branch: `s[i] != 0` is read from the same full array, `i` is within the payload when the branch continues, and after `i++` the bound remains `0 <= i <= n`.  The full array resource is read-only and remains unchanged.

The exit path needs to bridge from `s[i] == 0` to `i == n`.  With the invariant, if `i < n` then the array read corresponds to `l[i]`, but the precondition fact says `l[i] != 0`, contradicting the break condition.  Since the invariant also has `i <= n`, the only possible break index is `i == n`, where the terminator in `app(l, cons(0, nil))` is read.  I will add the following loop-exit assertion immediately after the loop, before local cleanup at return:

```c
/*@ Assert
      i == n &&
      n < INT_MAX &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion directly supplies the return value equality and preserves the heap predicate needed by the function postcondition.
