## 2026-04-23 annotation pass 1

Program point: the active annotated file initially matched `input/string_remove_char_to_output.c` and had no annotation before the only `while (1)` loop. The implementation initializes `i = 0` and `j = 0`, then repeatedly reads `s[i]`. If `s[i] == 0`, it exits; if `s[i] != c`, it writes `out[j] = s[i]` and increments `j`; every continuing iteration increments `i`. After the loop it writes the output terminator `out[j] = 0` and returns `j`.

The contract requires the input array to remain exactly `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. The output postcondition is expressed as the filtered Coq list `string_remove_char_to_output_spec(l, c@pre)`, followed by a zero terminator and an unconstrained suffix of length `n@pre - Zlength(string_remove_char_to_output_spec(l, c@pre))`. Without a loop invariant, symbolic execution has no stable relation between the processed input prefix, the output prefix already written, and the scalar index `j`.

The loop-head state should use the standard scan-prefix split:

```c
/*@ Inv exists l1 l2 d1,
      0 <= i && i <= n &&
      0 <= j && j <= i &&
      s == s@pre &&
      out == out@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      j == Zlength(string_remove_char_to_output_spec(l1, c)) &&
      Zlength(d1) == n + 1 - j &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, app(string_remove_char_to_output_spec(l1, c), d1))
*/
```

Here `l1` is the already processed input prefix and `l2` is the unprocessed suffix, so `i == Zlength(l1)` means the next read is exactly at the boundary. The output buffer is modeled as the filtered result for `l1` followed by a remaining suffix `d1`; `j == Zlength(string_remove_char_to_output_spec(l1, c))` identifies the next write position. The facts `s == s@pre`, `out == out@pre`, and `c == c@pre` preserve the parameter values needed by the postcondition, while the nonzero-prefix assumption is carried for the loop-exit proof.

Initialization: after `i = 0` and `j = 0`, choose `l1 = nil`, `l2 = l`, and `d1 = d`. The contract gives the full input and output resources, `0 <= n`, and the nonzero-prefix fact. Since `string_remove_char_to_output_spec(nil, c) = nil`, `j == Zlength(...)` is `0 == 0`, and the output heap remains `CharArray::full(out, n + 1, app(nil, d))`, equivalent to the precondition resource.

Preservation: on a continuing iteration, the branch fact `s[i] != 0` plus the input heap and the split `l == app(l1, l2)` expose the next input character. If `s[i] == c`, the filtered prefix does not grow, `j` stays unchanged, and after `i++` the new processed prefix is the old `l1` plus that character. If `s[i] != c`, the write updates the first cell of `d1`, `j++` advances to the new filtered-prefix length, and after `i++` the new processed prefix is again old `l1` plus the current character. In both branches the input heap is unchanged and the output heap remains a filtered prefix followed by a suffix.

Exit usefulness: when `s[i] == 0`, the invariant gives `0 <= i <= n`. If `i < n`, the precondition fact `(forall k, 0 <= k && k < n => l[k] != 0)` contradicts the observed zero at `s[i]`; therefore `i == n`, so the processed prefix is the whole `l`, and `j == Zlength(string_remove_char_to_output_spec(l, c))`. Immediately before `out[j] = 0`, I will add a focused assertion exposing the first suffix cell:

```c
/*@ Assert exists x t,
      i == n &&
      s == s@pre &&
      out == out@pre &&
      c == c@pre &&
      0 <= j && j <= n &&
      j == Zlength(string_remove_char_to_output_spec(l, c)) &&
      Zlength(t) == n - j &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, app(app(string_remove_char_to_output_spec(l, c), cons(x, nil)), t))
*/
```

This assertion is placed directly after the loop, before the terminating write, while local variables and heap permissions are still present. It converts the generic suffix `d1` into `cons(x, nil) ++ t`, so `out[j] = 0` can rewrite the output buffer into the postcondition shape with terminator `0` and suffix `t`.
