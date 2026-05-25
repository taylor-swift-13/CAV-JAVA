# Annotation reasoning

## Initial scan invariant for `string_find_char`

Current annotated C before this edit has no invariant around the only loop:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        return i;
    }
    i++;
}

return -1;
```

The loop is a left-to-right string scan. At the loop head, `i` is the next character position to inspect and the processed prefix is `[0, i)`. The postcondition has two first-match cases:

- If the function returns from inside the loop, it must prove `0 <= i < n`, `l[i] == c`, and every earlier `l[j]` differs from `c`.
- If the function reaches the final `return -1`, it must prove every `l[j]` for `0 <= j < n` differs from `c`.

Therefore the invariant must preserve exactly the scan history:

```c
/*@ Inv Assert
      0 <= i && i <= n &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
while (1) {
```

Initialization is immediate because `i == 0`, so the processed-prefix fact is vacuous and the original `CharArray::full` resource is unchanged. Preservation follows from the path that continues past both tests: `s[i] != 0`, `s[i] != c`, and `i < n` because the null terminator is at index `n` while every logical character before `n` is nonzero. After `i++`, the prefix `[0, i + 1)` differs from `c`.

The final `return -1` path also needs the loop-exit fact exposed at the right control point. When the first branch breaks, the current character is zero. Combined with `0 <= i <= n`, `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, and the precondition that every `l[k]` for `k < n` is nonzero, this should imply `i == n`. I will add a minimal assertion immediately after the loop:

```c
/*@ Assert
      i == n &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
return -1;
```

This assertion is intentionally placed before the final return, not after local-variable cleanup. It converts the invariant's processed-prefix fact at `i` into the full-range no-match fact by first fixing `i == n`.

## Add the missing `n < INT_MAX` bound after first `symexec`

Fresh `symexec` succeeded, but the generated manual goal `string_find_char_safety_wit_4` showed that the invariant was too weak for the increment safety check:

```coq
Definition string_find_char_safety_wit_4 :=
forall ... (n : Z) ... (i : Z),
  [| Znth i (l ++ 0 :: nil) 0 <> c_pre |] &&
  [| Znth i (l ++ 0 :: nil) 0 <> 0 |] &&
  [| 0 <= i |] &&
  [| i <= n |] &&
  [| Zlength l = n |] &&
  ...
|--
  [| i + 1 <= INT_MAX |] && ...
```

The original contract has `n < INT_MAX`, and the invariant has `i <= n`, so `i + 1 <= INT_MAX` is semantically immediate. The problem is that the first invariant did not carry `n < INT_MAX`, so this fact was absent from the generated safety witness. This is an annotation issue, not a Coq helper issue.

I will add `n < INT_MAX` to both the loop invariant and the loop-exit assertion. The revised loop invariant starts:

```c
/*@ Inv Assert
      0 <= i && i <= n &&
      n < INT_MAX &&
      ...
*/
```

The exit assertion also keeps `n < INT_MAX` so the final generated state remains aligned with the invariant-carried bounds. After this edit, I will clear the generated Coq files and rerun `symexec`; the resulting safety witness should contain the missing bound and become arithmetic.
