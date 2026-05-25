## 2026-04-22 03:13:45 +0800 - Prefix-count invariant for array_count_even

Current active annotated file initially has no Verify annotation around the `for` loop:

```c
int i;
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] % 2 == 0) {
        cnt++;
    }
}

return cnt;
```

The contract requires `__return == array_count_even_spec(l)` and `IntArray::full(a, n, l)`.  The loop scans the array from left to right, and at the loop guard control point `i` is the number of already processed elements and also the next index to read.  Therefore the accumulator invariant should describe the processed prefix exactly:

```c
cnt == array_count_even_spec(sublist(0, i, l))
```

The invariant must also keep the array heap predicate and stable parameter equalities because the return postcondition is written over the original parameters and full list:

```c
0 <= i && i <= n &&
a == a@pre &&
n == n@pre &&
cnt == array_count_even_spec(sublist(0, i, l)) &&
IntArray::full(a, n, l)
```

Initialization: after `cnt = 0` and `for (i = 0; ...)` initialization, the processed prefix is `sublist(0, 0, l)`, so the spec unfolds to 0 and the invariant matches `cnt`.

Preservation: in one iteration, the body reads `a[i]`.  If `a[i] % 2 == 0`, `cnt++` corresponds to the head contribution `1` for the newly appended element of the processed prefix; otherwise `cnt` remains the prefix count.  The array is read-only, so `IntArray::full(a, n, l)` remains unchanged.

Exit usability: after the loop exits, `i < n` is false and the invariant gives `i <= n`, so `i == n`.  A loop-exit assertion directly records that `cnt == array_count_even_spec(l)` and preserves the array predicate before local-variable cleanup:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_even_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

This should give symexec enough information to generate VCs for the prefix extension and the final return witness, leaving any list/arithmetic facts to Coq proof if automation cannot solve them.
