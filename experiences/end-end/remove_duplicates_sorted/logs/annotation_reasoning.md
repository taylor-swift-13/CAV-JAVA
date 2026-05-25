## 2026-04-22 21:18 CST - Initial loop invariant plan

Program point: the active annotated copy `annotated/verify_20260422_211833_remove_duplicates_sorted.c` currently reaches `for (i = 1; i < n; ++i)` with no `Inv`. The target function has already returned on `n == 0`; on the remaining path `j = 1` and the for-loop initialization makes `i = 1` before checking `i < n`.

Current issue before editing: symbolic execution needs a loop-head summary for the two-pointer in-place compaction. The postcondition requires the final prefix `sublist(0, __return, lr)` to equal `remove_duplicates_sorted_spec(l)`, while allowing the rest of the full array list `lr` to be existential. Without an invariant, the verifier cannot connect the current write index `j`, the processed prefix `sublist(0, i, l)`, and the modified heap list.

Planned annotation at the loop guard:

```c
/*@ Inv exists lc,
      1 <= i && i <= n@pre &&
      1 <= j && j <= i &&
      a == a@pre &&
      n == n@pre &&
      Zlength(lc) == n@pre &&
      j == Zlength(remove_duplicates_sorted_spec(sublist(0, i, l))) &&
      (forall (k: Z),
        (0 <= k && k < j) =>
        lc[k] == remove_duplicates_sorted_spec(sublist(0, i, l))[k]) &&
      (forall (k: Z),
        (i <= k && k < n@pre) =>
        lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

Why this invariant should initialize: after the nonzero branch, `Zlength(l) == n`, `n > 0`, `j == 1`, and the loop initialization sets `i == 1`. The current heap list is still the original `l`, so choose `lc = l`. The processed prefix is the first element, so `remove_duplicates_sorted_spec(sublist(0, 1, l))` has length 1 and its only element matches `l[0]`; the suffix preservation fact is immediate because no memory has been written yet.

Why this invariant should be preserved: when `i < n`, the suffix fact gives `lc[i] == l[i]`, so the read `a[i]` is related to the original next input. The prefix fact and `j == Zlength(...)` relate `a[j - 1]` to the last retained element of the deduplicated processed prefix. If the two values differ, the write `a[j] = a[i]` appends the new unique value to the retained prefix and increments `j`; if equal, the current heap list and `j` remain a valid summary of the larger processed prefix. In both branches the unread suffix from the next `i` through `n - 1` still equals the original list.

Why this invariant should be useful at exit: when the loop exits, `i == n@pre`. Since `n == n@pre` and `Zlength(l) == n`, `sublist(0, i, l)` is the full original list. The invariant then gives `j == Zlength(remove_duplicates_sorted_spec(l))` and pointwise prefix equality between the final heap list `lc` and `remove_duplicates_sorted_spec(l)`, which is exactly the return contract shape with `lr = lc`.

