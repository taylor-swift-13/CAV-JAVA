# Annotation Reasoning

## 2026-04-23 invariant for `string_replace_char`

Current annotated file contains the original contract and loop body but no loop invariant:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == old_c) {
        s[i] = new_c;
    }
    i++;
}
```

The input contract owns `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, where `l` is the nonzero payload of length `n` and the final cell is the zero terminator. The postcondition needs an existential payload `lr` of length `n` such that every original `old_c` is replaced by `new_c`, every other original character is preserved, every payload character remains nonzero, and the same buffer is returned as `app(lr, cons(0, nil))`.

At the top of the `while (1)` loop, before reading `s[i]`, the variable `i` denotes the length of the processed prefix and the next cell to inspect. The buffer should be modeled as `app(l1, l2)`, where `l1` is the transformed prefix of length `i`, and `l2` is the still-original suffix of length `n + 1 - i` containing the remaining payload characters plus the terminator. The invariant to add is:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      s == s@pre &&
      old_c == old_c@pre &&
      new_c == new_c@pre &&
      n@pre == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre + 1 - i &&
      (forall (t: Z),
        (0 <= t && t < i) =>
        ((l[t] == old_c => l1[t] == new_c) &&
         (l[t] != old_c => l1[t] == l[t]))) &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] != 0) &&
      (forall (t: Z), (0 <= t && t < n@pre + 1 - i) => l2[t] == app(l, cons(0, nil))[i + t]) &&
      CharArray::full(s, n@pre + 1, app(l1, l2))
*/
```

Initialization: after `int i = 0`, choose `l1 = nil` and `l2 = app(l, cons(0, nil))`. The processed-prefix value and nonzero conditions are vacuous, `Zlength(l1) == 0`, `Zlength(l2) == n + 1`, and the heap resource is exactly the precondition.

Preservation: assume the invariant and the loop does not break. The read `s[i] != 0` rules out the terminator and should combine with the suffix relation to keep `i < n@pre`. If `s[i] == old_c`, the assignment writes `new_c`, which is nonzero by the precondition, so the next `l1` extends the processed prefix with `new_c` and satisfies the replacement implication. If `s[i] != old_c`, no write occurs and the current original character `l[i]` remains in the buffer, so the next `l1` extends with `l[i]` and satisfies the preservation implication. In both branches, `i++` shifts one original suffix cell into the processed prefix, leaving the remaining suffix unchanged and still equal to the corresponding tail of `app(l, cons(0, nil))`.

Exit usability: when the loop breaks, `s[i] == 0`. The invariant says the suffix is still original; for every payload index `k < n`, the original `l[k]` is nonzero, while the only zero in `app(l, cons(0, nil))` is at index `n`. Together with `0 <= i <= n`, the break condition should establish `i == n`. Then `l2` has length one and equals `cons(0, nil)`, while `l1` has length `n` and satisfies exactly the postcondition payload relation. The final postcondition can choose `lr = l1`.

## 2026-04-23 parser repair for suffix expression

The first `symexec` run failed before VC generation:

```text
fatal error: Expected C expression in annotated/verify_20260423_033114_string_replace_char.c:23:1
Now parsing : n with type :2
```

The failing invariant used indexed access into an `app(...)` expression:

```c
(forall (t: Z), (0 <= t && t < n@pre + 1 - i) => l2[t] == app(l, cons(0, nil))[i + t])
```

The semantic idea is correct, but this front end is more stable when suffix facts over a null-terminated string are split into payload and terminator facts instead of indexing directly into `app(l, cons(0, nil))`. I am replacing the suffix assertion with two simpler facts:

```c
(forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == l[i + t]) &&
l2[n@pre - i] == 0
```

This keeps the same meaning at the loop head. The unprocessed payload part `l2[0..n-i)` equals the corresponding original payload `l[i..n)`, and the last suffix cell `l2[n-i]` is the unchanged zero terminator. Initialization still chooses `l1 = nil` and `l2 = app(l, cons(0, nil))`; preservation shifts one payload character from `l2` into `l1` and leaves the terminator fact at the new suffix end; exit still derives `i == n` from the break read `s[i] == 0` plus nonzero original payload, then `l2[0] == 0`.

## 2026-04-23 retry parser repair for ghost length `n`

The retry state has no generated Coq files because `symexec` still fails while parsing the active annotated contract:

```text
fatal error: Expected C expression in annotated/verify_20260423_033114_string_replace_char.c:23:1
Now parsing : n with type :2
```

The concrete parser blocker is the postcondition applying `@pre` to the ghost `With` variable `n`:

```c
Ensure
  exists lr,
    Zlength(lr) == n@pre &&
    (forall (i: Z),
      (0 <= i && i < n@pre) =>
      ((l[i] == old_c@pre => lr[i] == new_c@pre) &&
       (l[i] != old_c@pre => lr[i] == l[i]))) &&
    (forall (k: Z), (0 <= k && k < n@pre) => lr[k] != 0) &&
    CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
```

`n` is not a mutable C parameter or local variable; it is introduced by `With l n`. The nearby string examples such as `examples/string_contains_char/annotated/string_contains_char.c` keep ghost lengths as `n` in postconditions:

```c
Ensure
  (__return == 0 || __return == 1) &&
  CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

I am changing only the active annotated copy, not `input/string_replace_char.c`, so that `symexec` can parse and generate the actual VCs for this retry. The intended semantic length is unchanged: every occurrence of `n@pre` that refers to the ghost payload length becomes `n`. C parameters and locals still use `@pre` where needed; for example `old_c@pre`, `new_c@pre`, and `s@pre` remain because those are real C-state values. The loop invariant will also use direct `n` for the ghost length:

```c
0 <= i && i <= n &&
n == Zlength(l) &&
Zlength(l2) == n + 1 - i &&
(forall (t: Z), (0 <= t && t < n - i) => l2[t] == l[i + t]) &&
l2[n - i] == 0 &&
CharArray::full(s, n + 1, app(l1, l2))
```

Initialization, preservation, and exit reasoning remain the same as in the previous invariant note; this edit only removes unsupported `@pre` syntax on a ghost variable so the annotation can be parsed.
