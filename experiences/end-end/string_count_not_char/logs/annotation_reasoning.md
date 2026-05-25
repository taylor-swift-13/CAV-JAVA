# Annotation Reasoning

## 2026-04-23 prefix count invariant for `string_count_not_char`

Program point: the only loop is the `while (1)` immediately after local initialization in `annotated/verify_20260423_005835_string_count_not_char.c`. The formal contract states `0 <= n`, `n < INT_MAX`, `Zlength(l) == n`, each real character `l[k]` for `0 <= k < n` is nonzero, and the heap owns `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. The implementation is read-only: it scans `s[i]`, breaks on the terminating zero, increments `count` exactly when `s[i] != c`, increments `i`, and returns `count`.

Current annotated loop has no invariant:

```c
int i = 0;
int count = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] != c) {
        count++;
    }
    i++;
}
```

This is too weak for both symbolic execution and the final return witness. At the loop head, `i` is the next index to inspect and `count` summarizes exactly the processed prefix. The stable loop state should therefore split `l` into processed and unprocessed pieces `l1` and `l2`, keep `Zlength(l1) == i`, and relate `count` to `string_count_not_char_spec(l1, c)`. The heap does not change, so the invariant should keep the full original `CharArray::full` resource rather than a transformed resource. The invariant also keeps `s == s@pre`, `c == c@pre`, `Zlength(l) == n`, and the no-internal-zero assumption because those facts are needed to derive that a zero read can only occur at `i == n`.

Planned invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= count && count <= i &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      count == string_count_not_char_spec(l1, c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
while (1) {
```

Initialization: after `i = 0` and `count = 0`, choose `l1 = nil` and `l2 = l`. Then `0 <= i && i <= n` follows from `0 <= n`, `0 <= count && count <= i` is `0 <= 0 <= 0`, `l == app(nil, l)` and `Zlength(nil) == 0` are immediate, and `string_count_not_char_spec(nil, c) == 0` matches `count`. The unchanged pointer/value facts, length fact, nonzero-prefix fact, and full string heap resource are exactly the precondition plus local stores.

Preservation: when the loop continues, the branch fact `s[i] != 0` means `i < n`, because if `i == n` then the `CharArray::full` resource and `l ++ [0]` terminator make `s[i]` equal to `0`; if `i < n`, the original contract already says the logical character is nonzero. If `s[i] != c`, incrementing `count` corresponds to the recursive step of `string_count_not_char_spec` adding `1` for the newly processed character. If `s[i] == c`, `count` stays unchanged, corresponding to the recursive step adding `0`. In both branches, incrementing `i` extends `l1` by the current character, so `Zlength(l1) == i` is restored for the next loop head. The array resource and parameter equalities remain unchanged because the loop only reads from `s`.

Exit usefulness: on the `s[i] == 0` break path, the invariant gives `i <= n`. The no-internal-zero fact rules out `i < n`, so `i == n`; from `Zlength(l1) == i`, `Zlength(l) == n`, and `l == app(l1, l2)`, the unprocessed suffix `l2` is empty. Therefore `count == string_count_not_char_spec(l1, c)` becomes the postcondition relation `count == string_count_not_char_spec(l, c)`, and the unchanged `CharArray::full` resource directly matches the postcondition heap.
