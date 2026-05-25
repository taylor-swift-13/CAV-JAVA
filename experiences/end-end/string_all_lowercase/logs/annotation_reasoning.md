## 2026-04-22 annotation iteration 1

Program point: immediately before the `while (1)` loop in `annotated/verify_20260422_223908_string_all_lowercase.c`.

Current unannotated loop:
```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] < 97 || s[i] > 122) {
        return 0;
    }
    i++;
}
```

Why an invariant is needed: the loop scans the string one byte at a time and may either return early on a non-lowercase byte or break at the terminating 0. The postcondition mentions `string_all_lowercase_spec(l)`, so the verifier must retain a semantic summary of the already-scanned prefix. Without an invariant, symbolic execution has no stable loop state describing the processed prefix, the current index bound, or the preserved `CharArray::full` resource.

Planned invariant:
```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_all_lowercase_spec(l1) == 1 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Initialization: before the first loop test, `i == 0`; choosing `l1 = nil` and `l2 = l` gives `l == app(nil, l)`, `Zlength(nil) == 0`, and `string_all_lowercase_spec(nil) == 1`. The original precondition supplies the nonzero-before-terminator fact and the full char-array heap resource.

Preservation: when the current byte is nonzero and in range `97..122`, the next iteration has consumed exactly one more lowercase element. The split can move the current element from `l2` to the end of `l1`, `i` increases by one, and the lowercase spec of the new prefix remains `1`. The function does not write memory, so the same `CharArray::full` resource is preserved.

Early return branch: if the current byte is outside `97..122`, the current list element makes `string_all_lowercase_spec(l) == 0` after unfolding across the known-good prefix, so returning `0` is semantically aligned with the postcondition while preserving the heap.

Loop exit branch: if `s[i] == 0`, the precondition fact that every `l[k]` for `k < n` is nonzero and `i <= n` should force `i == n`; with `l2 == nil`, the whole list is the processed prefix and `string_all_lowercase_spec(l) == 1`, matching `return 1`.

