## Annotation iteration 1: add prefix-fill invariant for the for loop

Program point: `string_set_a` has one mutating loop:

```c
for (i = 0; i < n; ++i) {
    s[i] = 97;
}
s[n] = 0;
```

The input contract gives `0 <= n`, `n < INT_MAX`, `Zlength(l) == n + 1`, and `CharArray::full(s, n + 1, l)`. The postcondition requires an output list `lr` of the same length where every prefix position `0 <= k < n` has value `97`, position `n` has value `0`, and the whole `CharArray::full(s, n + 1, lr)` resource is returned.

The loop variable `i` is the next index to write, so at the loop control point the processed prefix is `[0, i)`. The invariant must keep:

```c
exists lr,
  0 <= i && i <= n@pre &&
  s == s@pre &&
  n == n@pre &&
  Zlength(lr) == n@pre + 1 &&
  (forall (k: Z), (0 <= k && k < i) => lr[k] == 97) &&
  (forall (k: Z), (i <= k && k < n@pre + 1) => lr[k] == l[k]) &&
  CharArray::full(s, n@pre + 1, lr)
```

Initialization: after `i = 0`, the processed-prefix implication is vacuous, the suffix condition covers the whole buffer and matches the pre-state list `l`, and the precondition supplies `CharArray::full(s, n + 1, l)`. The bounds hold from `0 <= n`.

Preservation: when the loop condition gives `i < n`, the assignment `s[i] = 97` updates exactly the next cell. The new logical list can be `replace_Znth i 97 lr`; the prefix property extends from `[0, i)` to `[0, i + 1)`, and the suffix preservation shifts from `[i, n + 1)` to `[i + 1, n + 1)`. The unchanged facts `s == s@pre` and `n == n@pre` remain stable.

Exit usability: when the loop exits, the invariant gives `i == n` from `0 <= i <= n@pre`, `n == n@pre`, and `!(i < n)`. The final assignment `s[n] = 0` then updates the terminator cell while preserving the established prefix property, producing exactly the postcondition shape.

Before annotation:

```c
int i;

for (i = 0; i < n; ++i) {
    s[i] = 97;
}
s[n] = 0;
```

Planned annotation:

```c
int i;

/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      s == s@pre &&
      n == n@pre &&
      Zlength(lr) == n@pre + 1 &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == 97) &&
      (forall (k: Z), (i <= k && k < n@pre + 1) => lr[k] == l[k]) &&
      CharArray::full(s, n@pre + 1, lr)
*/
for (i = 0; i < n; ++i) {
    s[i] = 97;
}
s[n] = 0;
```
