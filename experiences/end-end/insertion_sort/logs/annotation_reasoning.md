## 2026-04-22 17:43 +0800 - Initial insertion-sort invariant plan

Program point: the active annotated file `annotated/verify_20260422_174132_insertion_sort.c` currently matches the input and has no loop invariants:

```c
for (i = 1; i < n; ++i) {
    key = a[i];
    j = i - 1;
    while (j >= 0 && a[j] > key) {
        a[j + 1] = a[j];
        j--;
    }
    a[j + 1] = key;
}
```

This is insufficient for symbolic execution because the function mutates `IntArray::full(a, n, l)` in place while the postcondition requires a final list `lr` with `insertion_sort_spec(l, lr)`, i.e. `StronglySorted Z.le lr` and `Permutation l lr`. Without an outer invariant there is no current ghost list for the array or permutation relation to the original list. Without an inner invariant the temporary state after `key = a[i]` is not a normal insertion-sort array: the value `key` is held in a scalar and the array segment is shifted right, leaving a logical hole.

Planned outer-loop annotation:

```c
/*@ Inv exists l_outer,
      1 <= i && i <= n@pre + 1 &&
      (n@pre > 0 => i <= n@pre) &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l_outer) == n@pre &&
      Permutation(l, l_outer) &&
      (forall (k: Z),
        (0 <= k && k + 1 < i) => l_outer[k] <= l_outer[k + 1]) &&
      IntArray::full(a, n@pre, l_outer)
*/
```

The invariant is located at the `for` loop condition, after `i = 1` and before `i < n` is tested. Therefore `i <= n@pre` would be invalid for the allowed skip case `n == 0`; the bound must be widened to `i <= n@pre + 1`, with the conditional fact `(n@pre > 0 => i <= n@pre)` to recover the exact exit state for nonempty arrays. The semantic fact is adjacent-prefix order over `[0, i)`, not a global prefix-to-suffix ordering: insertion sort does not guarantee every processed prefix element is less than every unprocessed suffix element. Initialization holds with `l_outer = l` because the prefix of length one has no adjacent pair. Preservation after the final insertion should establish adjacent order over `[0, i + 1)`, while permutation and heap ownership move to the updated array list. At loop exit, adjacent order over the whole list can be converted in Coq to the sorted part of `insertion_sort_spec`.

Planned inner-loop annotation:

```c
/*@ Inv exists l_cur l_base,
      1 <= i && i < n@pre &&
      -1 <= j && j < i &&
      key == l_base[i] &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l_base) == n@pre &&
      Permutation(l, l_base) &&
      (forall (k: Z),
        (0 <= k && k + 1 < i) => l_base[k] <= l_base[k + 1]) &&
      (forall (k: Z),
        (j < k && k < i) => key < l_base[k]) &&
      l_cur == app(sublist(0, j + 2, l_base),
                   app(sublist(j + 1, i, l_base),
                       sublist(i + 1, n@pre, l_base))) &&
      IntArray::full(a, n@pre, l_cur)
*/
```

The inner invariant explicitly models the shifted-hole state. `l_base` is the outer-loop array before taking `key`, and `l_cur` is the current heap list. The expression `sublist(0, j + 2, l_base) ++ sublist(j + 1, i, l_base) ++ sublist(i + 1, n@pre, l_base)` records that positions after `j` and before `i` have been shifted right while `key = l_base[i]` is outside the array. The quantified fact `(j < k && k < i) => key < l_base[k]` is initialized vacuously at `j = i - 1`; every loop iteration shifts `l_base[j]` right under the guard `a[j] > key`, extending this fact to the new hole boundary `j - 1`. On inner-loop exit, either `j < 0` or `a[j] <= key`; together with the shifted-elements fact and adjacent-prefix order on `l_base`, this gives a local adjacent-order proof for the final write `a[j + 1] = key`.

I will add only these two invariants to the active annotated C, then clear any generated Coq files in the current workspace and rerun `symexec`. If the remaining obligations are pure shifted-hole, permutation, adjacent-order, or sortedness conversion lemmas, they belong to `proof_manual.v` rather than another annotation rewrite.

## 2026-04-22 17:44 +0800 - Declare direct `Permutation` annotation symbol

After adding the invariants, the first `symexec` run failed before VC generation with:

```text
fatal error: Use of undeclared identifier `Permutation' in QCP_examples/CAV/annotated/verify_20260422_174132_insertion_sort.c:37:4
```

The contract imports `insertion_sort_spec`, and `input/insertion_sort.v` defines that spec using Coq's `Permutation`, but the C annotation language still needs a direct external declaration when `Permutation(l, l_outer)` appears in an invariant. This is not a contract redesign; it is a front-end symbol declaration needed by the active annotated copy.

I will add:

```c
/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */
```

near the existing `Extern Coq` and `Import Coq` lines, then rerun `symexec` after clearing generated files. The invariant semantics remain unchanged.
