## 2026-04-23 12:09 initial loop invariant

Current program point:

```c
int i = 0;

while (1) {
    if (s[i + 1] == 0) {
        break;
    }
    i++;
}

return s[i];
```

The loop scans a nonempty string whose logical payload is `l` and whose terminator is at index `n`. The postcondition needs `__return == l[n - 1]` and the unchanged `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. Therefore the loop invariant must keep the full heap resource and enough pure information to show that the break happens exactly when `i == n - 1`.

The chosen invariant is:

```c
/*@ Inv Assert
      1 <= n && n < INT_MAX && 0 <= i && i < n &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization: after `int i = 0`, the precondition has `1 <= n`, so `0 <= i && i < n` holds. The full array resource and logical list facts are exactly the precondition, and `s == s@pre` records that the pointer parameter is unchanged.

Preservation: at the loop head, `0 <= i && i < n`. If `s[i + 1] != 0`, then `i + 1` cannot be the terminator index `n`; because every payload index `< n` is nonzero and the array is `l ++ [0]`, the next loop state after `i++` still has `i < n`. The heap resource is read-only and remains unchanged.

Exit usefulness: if the break branch sees `s[i + 1] == 0`, the only zero in the modeled string is the terminator after the nonzero prefix, so `i + 1 == n`, hence `i == n - 1`. A loop-exit assertion will record this fact immediately after the loop:

```c
/*@ Assert
      1 <= n &&
      n < INT_MAX &&
      i == n - 1 &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion is placed before `return s[i]`, while the local variable permission for `i` is still live. It bridges the loop state to the return read: with `i == n - 1` and the full `CharArray`, reading `s[i]` corresponds to `l[n - 1]`, which is exactly the return postcondition.
