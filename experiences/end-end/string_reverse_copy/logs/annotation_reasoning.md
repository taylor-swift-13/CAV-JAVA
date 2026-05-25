## Annotation iteration 1

Current program point: the only loop is

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[n - 1 - i];
}
dst[n] = 0;
```

The active annotated copy currently has no `Inv`, so `symexec` would not have a stable heap shape at the loop head. The postcondition requires `dst` to contain `app(rev(l), cons(0, nil))`, but before the final `dst[n] = 0` statement the loop has only written the first `n` cells. The invariant therefore must describe the destination buffer as a processed prefix plus the still-old suffix.

The loop variable `i` is the number of destination cells already written. At the loop head:

- `0 <= i <= n@pre`.
- `src`, `dst`, and `n` must remain equal to their pre-state values because the postcondition is stated over the original buffers and length.
- `src` remains `CharArray::full(src, n@pre + 1, app(l, cons(0, nil)))`.
- `dst` is split as `app(rev(sublist(n@pre - i, n@pre, l)), sublist(i, n@pre + 1, d))`. The prefix length is `i`; it is exactly the reverse of the source suffix already consumed by reads at indexes `n - 1`, `n - 2`, ..., `n - i`. The suffix is the original destination from `i` through `n`, so the final terminator slot remains available for `dst[n] = 0`.

Initialization: when `i == 0`, `sublist(n, n, l)` is empty and the destination expression reduces to `d`, matching the original precondition.

Preservation: assuming the invariant and loop condition `i < n`, the assignment `dst[i] = src[n - 1 - i]` appends the source element at `n - 1 - i` to the processed prefix. This converts `rev(sublist(n - i, n, l))` into `rev(sublist(n - (i + 1), n, l))` after the `++i` step, while the destination suffix advances from `sublist(i, n + 1, d)` to `sublist(i + 1, n + 1, d)`.

Exit usability: when the loop exits, the `for` condition gives `i >= n` and the invariant gives `i <= n`, so `i == n`. The destination heap is then `app(rev(sublist(0, n, l)), sublist(n, n + 1, d))`, and since `Zlength(l) == n`, this is `app(rev(l), sublist(n, n + 1, d))`. The following statement `dst[n] = 0` overwrites the single remaining slot, yielding `app(rev(l), cons(0, nil))`.

I will add the following invariant immediately before the `for` loop:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      src == src@pre &&
      dst == dst@pre &&
      n == n@pre &&
      Zlength(l) == n@pre &&
      Zlength(d) == n@pre + 1 &&
      (forall (k: Z), (0 <= k && k < n@pre) => l[k] != 0) &&
      CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n@pre + 1,
        app(rev(sublist(n@pre - i, n@pre, l)), sublist(i, n@pre + 1, d)))
*/
```

## Annotation iteration 2

The first `symexec` run after adding the invariant failed before VC generation:

```text
fatal error: Use of undeclared identifier `sublist' in annotated/verify_20260423_041041_string_reverse_copy.c:33:4
symexec_status=1
```

The failing annotation fragment is the destination heap in the loop invariant:

```c
CharArray::full(dst, n@pre + 1,
  app(rev(sublist(n@pre - i, n@pre, l)), sublist(i, n@pre + 1, d)))
```

This is not a semantic weakness of the invariant; the front end simply does not know the Coq symbol `sublist` in this annotated C file. The existing string prefix example under `examples/string_copy_prefix/annotated/string_copy_prefix.c` handles the same situation with:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

I will add that declaration immediately after the includes. This keeps the invariant unchanged and only makes the already-used list slicing symbol available to the parser.
