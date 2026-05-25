## 2026-04-22 05:15:14 CST - Initial two-pointer loop invariant

Current program point: the only loop is `while (i < n && j < m)` in the active annotated file `annotated/verify_20260422_051342_array_intersection_count_sorted.c`. The current working copy is identical to the contract input and has no loop invariant:

```c
int i = 0;
int j = 0;
int count = 0;
while (i < n && j < m) {
    if (a[i] == b[j]) {
        count++;
        i++;
        j++;
    } else if (a[i] < b[j]) {
        i++;
    } else {
        j++;
    }
}
return count;
```

Without an `Inv`, symbolic execution has no stable loop-head state connecting the already consumed prefixes, the unmodified arrays, and the recursive Coq specification `array_intersection_count_sorted_spec`. The key loop-head meaning is: `i` and `j` are the next positions in `la` and `lb`; `count` is the number of matches already consumed; and the remaining work is exactly the same specification over the suffixes `sublist(i, n, la)` and `sublist(j, m, lb)`.

Planned annotation:

```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= j && j <= m &&
      0 <= count && count <= i && count <= j &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      m == m@pre &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      (forall (x: Z) (y: Z),
        (0 <= x && x <= y && y < n) => la[x] <= la[y]) &&
      (forall (x: Z) (y: Z),
        (0 <= x && x <= y && y < m) => lb[x] <= lb[y]) &&
      count + array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb)) ==
        array_intersection_count_sorted_spec(la, lb) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
*/
while (i < n && j < m) { ... }
```

Why this should initialize: before the loop `i == 0`, `j == 0`, and `count == 0`; `sublist(0, n, la)` and `sublist(0, m, lb)` are the full lists because the precondition gives `Zlength(la) == n` and `Zlength(lb) == m`, so the semantic equality reduces to `0 + spec(la, lb) == spec(la, lb)`. The array ownership predicates are exactly the precondition predicates.

Why this should be preserved: at a loop iteration, the guard gives `i < n` and `j < m`, so both reads `a[i]` and `b[j]` are in range. If the elements are equal, the C code increments `count`, `i`, and `j`; the Coq spec over the two suffixes follows the equal branch and contributes one match before recurring on both tails. If `a[i] < b[j]`, sortedness of `la` and `lb` lets the recursive spec drop the current `la[i]` and continue with `i + 1, j`; the code also only increments `i`. If `a[i] > b[j]`, the spec drops the current `lb[j]`; the code only increments `j`. The bounds `count <= i` and `count <= j` are also preserved in all three branches and provide the signed-int overflow guard for `count++`.

Why this should be enough at exit: the negated guard gives `i >= n || j >= m`; with invariant bounds this means `i == n || j == m`. In either case one of the suffixes is empty, so `array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb))` is zero. The semantic invariant then yields `count == array_intersection_count_sorted_spec(la, lb)`, matching the return postcondition while the arrays remain unchanged.
