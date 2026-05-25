# Annotation Reasoning

## 2026-04-23 invariant for `string_to_upper_ascii`

The active annotated file initially matches the input contract and implementation, with no loop invariant before the string scan:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 97 && s[i] <= 122) {
        s[i] = s[i] - 32;
    }
    i++;
}
```

The precondition owns `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, where `l` is the nonzero payload and the final `0` is the terminator. The postcondition needs an existential payload `lr` of length `n` such that every original lowercase ASCII byte in `97..122` becomes `l[i] - 32`, every other byte is preserved, every payload byte remains nonzero, and the same buffer is returned as `app(lr, cons(0, nil))`.

At the head of the `while (1)` loop, before reading `s[i]`, `i` is the length of the processed prefix and the next cell to inspect. The heap should be represented as `app(l1, l2)`: `l1` is the already transformed prefix of length `i`, while `l2` is the still-original suffix of length `n + 1 - i`, including the remaining payload and final zero terminator. The invariant to add is:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      n == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n + 1 - i &&
      (forall (t: Z), (0 <= t && t < i && 97 <= l[t] && l[t] <= 122) => l1[t] == l[t] - 32) &&
      (forall (t: Z), (0 <= t && t < i && (l[t] < 97 || 122 < l[t])) => l1[t] == l[t]) &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] != 0) &&
      (forall (t: Z), (0 <= t && t < n - i) => l2[t] == l[i + t]) &&
      l2[n - i] == 0 &&
      CharArray::full(s, n + 1, app(l1, l2))
*/
```

Initialization: after `int i = 0`, choose `l1 = nil` and `l2 = app(l, cons(0, nil))`. The transformed-prefix facts and nonzero-prefix fact are vacuous, the suffix relation covers the whole original payload, and `l2[n] == 0` is exactly the terminator.

Preservation: assume the invariant at loop head and the `s[i] == 0` branch is not taken. Because the suffix still equals the original payload followed by the terminator, the nonzero read identifies a payload element and should imply `i < n`. If `97 <= s[i] && s[i] <= 122`, the assignment writes `s[i] - 32`, so the next prefix appends `l[i] - 32`; this is nonzero because the original payload character is in `97..122`. If the lowercase test is false, no write occurs and the next prefix appends the original `l[i]`; this is nonzero by the precondition. In both branches, `i++` moves one payload cell from the suffix into the processed prefix, preserves the remaining original suffix relation, and keeps the zero terminator at index `n - i` of the new suffix.

Exit usability: when the loop breaks, the read established `s[i] == 0`. The invariant says the suffix is original and that every original payload element `l[k]` for `0 <= k < n` is nonzero, so together with `0 <= i <= n` the break condition should establish `i == n`. Then `l2` has length one with `l2[0] == 0`, and `l1` has length `n` plus exactly the per-index uppercase/preserve relation required by the postcondition. The final postcondition can choose `lr = l1`.

The active annotated postcondition currently uses `n@pre` for the ghost `With` variable `n`:

```c
Ensure
  exists lr,
    Zlength(lr) == n@pre &&
    (forall (i: Z),
      (0 <= i && i < n@pre) => ...) &&
    (forall (k: Z), (0 <= k && k < n@pre) => lr[k] != 0) &&
    CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
```

Nearby verified string examples and the previous lowercase counterpart show that ghost lengths should remain `n`; `@pre` is for C-state variables and parameters. I will repair only the active annotated verification copy by replacing these ghost-length occurrences with direct `n`, leaving `input/string_to_upper_ascii.c` unchanged. This keeps the intended length semantics because `Zlength(l) == n` is a ghost fact and no statement mutates `n`.
