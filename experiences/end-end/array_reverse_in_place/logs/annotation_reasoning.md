## 2026-04-22 07:44:46 +0800 - Annotation round 1

Current program point: the only loop is `while (left < right)` after `left = 0` and `right = n - 1`. The unannotated loop gives symexec no invariant for the mutable `IntArray::full(a, n, l)` resource, so verification cannot preserve enough heap/value state to prove the final `IntArray::full(a, n, rev(l))` postcondition.

Relevant current C fragment before the edit:

```c
int left = 0;
int right = n - 1;

while (left < right) {
    int tmp = a[left];
    a[left] = a[right];
    a[right] = tmp;
    left++;
    right--;
}
```

Planned invariant: at the loop test, `left` is the number of processed elements on each side and `right` is the last unprocessed index. The concrete array list is split into three logical parts:

- prefix `rev(sublist(n@pre - left, n@pre, l))`, containing elements already moved from the original suffix;
- middle `sublist(left, right + 1, l)`, which has not yet been changed;
- suffix `rev(sublist(0, left, l))`, containing elements already moved from the original prefix.

The full heap predicate will therefore be:

```c
IntArray::full(a, n@pre,
  app(rev(sublist(n@pre - left, n@pre, l)),
    app(sublist(left, right + 1, l),
      rev(sublist(0, left, l)))))
```

Initialization: before the first test, `left == 0` and `right == n - 1`, so the processed prefix and suffix are empty, and `sublist(0, n, l)` is the original list. This also handles `n == 0`, where `right == -1` and the middle sublist is empty.

Preservation: under `left < right`, the loop swaps the endpoints of the middle segment, then advances to `left + 1` and `right - 1`. Because the invariant also states `right == n@pre - 1 - left`, the old `a[right]` is exactly the next element to append to the processed prefix and the old `a[left]` is exactly the next element to prepend to the processed suffix.

Exit usability: when the loop exits, `left >= right` together with `right == n@pre - 1 - left` means the unprocessed middle has length zero or one. The invariant should reduce the final list to `rev(l)` by list arithmetic; if that is not discharged automatically, it belongs to proof-level list lemmas rather than another annotation change, because the heap shape and all program semantics are present.

New annotated C fragment to insert before the loop:

```c
/*@ Inv
      0 <= left && left <= n@pre &&
      right == n@pre - 1 - left &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      IntArray::full(a, n@pre,
        app(rev(sublist(n@pre - left, n@pre, l)),
          app(sublist(left, right + 1, l),
            rev(sublist(0, left, l)))))
*/
while (left < right) {
```

## 2026-04-22 07:50:10 +0800 - Annotation round 2

Proof inspection of `array_reverse_in_place_return_wit_1` showed that the first invariant was too weak at loop exit. It recorded:

```c
0 <= left && left <= n@pre &&
right == n@pre - 1 - left
```

but it did not record the reachable crossing bound `left <= right + 1`. At loop exit we have `left >= right`; with the missing bound, the proof cannot restrict the unprocessed middle `sublist(left, right + 1, l)` to the real zero-or-one element cases. The arithmetic equation alone admits unreachable states such as `n = 5, left = 4, right = 0`, where `left >= right` and `right = n - 1 - left` hold but the current list expression is not forced to equal `rev(l)`.

This is an annotation issue, not a tactic issue, because the return witness lacks a program-state fact needed to derive the postcondition. The invariant should be strengthened at the loop test with:

```c
left <= right + 1
```

Initialization: with `left = 0` and `right = n - 1`, this becomes `0 <= n`, already guaranteed by the precondition.

Preservation: under the loop guard `left < right`, after `left++` and `right--`, the new fact is `left_old + 1 <= right_old`, which follows directly from `left_old < right_old` over integers.

Exit usability: combined with `left >= right`, the new fact gives `left == right` or `left == right + 1`, exactly the odd/even reversal stopping cases needed for the final `rev(l)` heap predicate.

Updated invariant fragment:

```c
/*@ Inv
      0 <= left && left <= n@pre &&
      left <= right + 1 &&
      right == n@pre - 1 - left &&
      ...
*/
```

