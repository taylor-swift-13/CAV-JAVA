## Annotation iteration 1

Current source state before this edit:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] != 0) {
        return 0;
    }
}

return 1;
```

The loop scans the array prefix `[0, i)` and returns early when it observes `a[i] != 0`. For verification, the key semantic fact after each completed iteration is that every index already scanned contains zero. The current annotated file has no `Inv`, so symbolic execution has no stable place to store this prefix fact, nor the unchanged parameter facts needed to return the same `IntArray::full(a, n, l)` resource from the precondition.

Planned invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] == 0) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }
```

This invariant is initialized by `i = 0`: the quantified prefix is empty, `0 <= n` is from the precondition, and the array resource is exactly the precondition resource. It is preserved across a normal iteration because reaching `++i` means the branch `a[i] != 0` was false, so the just-read element at the old index is zero; combined with the old prefix fact this proves the new prefix `[0, i + 1)` is all zero. It also preserves `a == a@pre`, `n == n@pre`, and the full array resource because the function only reads from `a`.

The early return branch occurs under `i < n` and `a[i] != 0`, while the invariant gives `0 <= i`; these facts provide the existential witness required by the `__return == 0` side of the postcondition, and the unchanged array resource discharges the heap part.

After the loop exits, `i < n` is false and the invariant has `i <= n`, so `i == n`. I will add a loop-exit `Assert` immediately after the loop to present the postcondition-facing form:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] == 0) &&
      IntArray::full(a, n, l)
*/
return 1;
```

This assertion is positioned before local cleanup at `return 1`, and converts the prefix fact at `i` into the full-array universal fact required by the `__return == 1` disjunct.
