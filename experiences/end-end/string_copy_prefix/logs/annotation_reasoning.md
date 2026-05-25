## 2026-04-23 annotation iteration 1

Current program point:

```c
int i;

for (i = 0; i < k; ++i) {
    dst[i] = src[i];
}
dst[k] = 0;
```

The input contract already supplies the heap resources:

```c
CharArray::full(src, n + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k + 1, d)
```

and the postcondition needs:

```c
CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k@pre + 1, app(sublist(0, k@pre, l), cons(0, nil)))
```

The loop copies one character per iteration from index `i`, so at the loop test point `i` is the number of characters already copied and also the next write index. The invariant must preserve the source array unchanged, split the destination into an already copied prefix and an untouched suffix, and retain enough pure facts to make the final `dst[k] = 0` write legal.

Planned invariant:

```c
/*@ Inv exists l1 d1,
      0 <= i && i <= k &&
      k <= n && n < INT_MAX &&
      src == src@pre &&
      dst == dst@pre &&
      k == k@pre &&
      Zlength(l) == n &&
      Zlength(l1) == i &&
      Zlength(d1) == k + 1 - i &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != 0) &&
      (forall (j: Z), (0 <= j && j < i) => l1[j] == l[j]) &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, k + 1, app(l1, d1))
*/
```

Initialization: after `for` initialization, `i == 0`; choosing `l1 = nil` and `d1 = d` satisfies `Zlength(l1) == 0` and `Zlength(d1) == k + 1`, while the copied-prefix `forall` is vacuous.

Preservation: when `i < k`, the invariant gives `i < n` from `i < k <= n`, so `src[i]` is inside `l` before the terminator. The assignment `dst[i] = src[i]` extends the copied prefix by one character and shrinks the remaining suffix by one; after `++i`, the new `Zlength(l1)` again matches the new `i`.

Exit: when the loop exits, the invariant gives `i <= k` and the negated guard gives `i >= k`, so `i == k`. The destination is split as `app(l1, d1)` with `Zlength(l1) == k` and `Zlength(d1) == 1`; writing `dst[k] = 0` should turn the last one-cell suffix into `cons(0,nil)`. The final proof may still need a list lemma to convert the pointwise prefix fact on `l1` into `l1 == sublist(0,k,l)`, but the heap shape and bounds should be available from this invariant.

## 2026-04-23 annotation iteration 2

The first `symexec` attempt did not reach loop invariant checking. It failed while parsing the supplied postcondition:

```text
fatal error: Use of undeclared identifier `sublist' in .../annotated/verify_20260423_000831_string_copy_prefix.c:19:1
```

The relevant contract fragment is:

```c
Ensure
  CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
  CharArray::full(dst, k@pre + 1,
    app(sublist(0, k@pre, l), cons(0, nil)))
```

The active file includes `verification_list.h` and `char_array_def.h`. `verification_list.h` declares `nil`, `cons`, `app`, `rev`, and `Zlength`; `char_array_def.h` declares `CharArray` predicates, `Znth`, `replace_Znth`, and `repeat_Z`, but not `sublist`. By contrast, `int_array_def.h` declares the same list helper:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

This is a parser symbol-declaration gap, not a change to the C implementation or the Require/Ensure formulas. The repair is to add the same `Extern Coq` declaration for `sublist` near the includes in the active annotated copy only:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

Expected effect: the existing postcondition and the later proof goals can refer to Coq's `sublist` symbol, allowing `symexec` to proceed to VC generation. The official `input/string_copy_prefix.c` remains unchanged.

## 2026-04-23 annotation iteration 3

After declaring `sublist`, `symexec` still failed before loop checking:

```text
fatal error: Expected C expression in .../annotated/verify_20260423_000831_string_copy_prefix.c:21:1
Now parsing : n with type :2
```

The only remaining complex expression in the function postcondition was:

```c
CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k@pre + 1,
  app(sublist(0, k@pre, l), cons(0, nil)))
```

This function never assigns to parameters `k`, `src`, or `dst`, and `n` is a ghost contract variable. The loop invariant already preserves:

```c
src == src@pre &&
dst == dst@pre &&
k == k@pre
```

The parser failure points to the frontend not accepting `@pre` inside the argument position of the newly declared polymorphic `sublist`. Existing verified examples commonly use unchanged parameters directly in postconditions, for example `string_copy` uses `n` instead of `n@pre`. I will normalize only the active annotated copy's postcondition to:

```c
CharArray::full(src, n + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k + 1,
  app(sublist(0, k, l), cons(0, nil)))
```

This keeps the intended mathematical post-state relation because the C function does not modify `k`, `src`, or the ghost list `l`; it is a parser-stability normalization in the Verify working copy. The official `input/string_copy_prefix.c` remains unchanged.
