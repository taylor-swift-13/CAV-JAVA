# Annotation Reasoning

## 2026-04-22 prefix/suffix loop invariant for `string_contains_char`

Program point: the only loop is the `while (1)` after `int i = 0;` in `string_contains_char`. The input contract gives `0 <= n`, `n < INT_MAX`, every real character `l[k]` for `0 <= k < n` is nonzero, and `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. The implementation is read-only: it inspects `s[i]`, breaks on the terminating zero, returns `1` when the current character equals `c`, and otherwise increments `i`.

Current annotated C has no invariant:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        return 1;
    }
    i++;
}

return 0;
```

This is too weak because the postcondition is stated through `string_contains_char_spec(l, c)`. At the loop head, `i` is the next index to inspect, so the stable semantic summary should be that the already scanned prefix contains no `c`. A previous archived run for this same program showed that writing this directly with `sublist(0, i, l)` can fail in the annotation front end with an undeclared `sublist`; the accepted shape is to expose the processed prefix and unprocessed suffix with existential lists.

Planned invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_contains_char_spec(l1, c) == 0 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
while (1) {
```

Initialization: immediately after `i = 0`, choose `l1 = nil` and `l2 = l`. The bounds `0 <= i && i <= n` follow from `0 <= n`, `l == app(nil, l)` is trivial, `Zlength(nil) == 0`, and `string_contains_char_spec(nil, c) == 0`. The unchanged facts `s == s@pre`, `c == c@pre`, the nonzero-prefix assumption, and the full character-array resource all come from the precondition and the local store.

Preservation: on a continuing iteration, the branch facts give `s[i] != 0` and `s[i] != c`. The heap fact connects `s[i]` to the current head of the suffix. Extending `l1` with that nonmatching character preserves `string_contains_char_spec(l1, c) == 0` for the next loop head, and `i++` makes the new `Zlength(l1)` equal the new `i`. The function still has not modified `s`, `c`, or the array resource.

Return usefulness: on the `s[i] == c` branch, the invariant gives a prefix `l1` with no earlier match, and the current suffix head equals `c`, so the full list spec evaluates to `1`. On the terminating-zero branch, the invariant gives `i <= n`; if `i < n`, the contract says the current logical character is nonzero, contradicting the read zero. Therefore `i == n`, the suffix must be empty, and `string_contains_char_spec(l, c)` follows from the prefix summary as `0`.
