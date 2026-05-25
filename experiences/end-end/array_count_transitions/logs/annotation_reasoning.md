# Annotation Reasoning

## Iteration 1: Prefix-transition invariant for the `i = 1` scan

Program point: the unannotated loop in `array_count_transitions`:

```c
int i;
int cnt = 0;

for (i = 1; i < n; ++i) {
    if (a[i] != a[i - 1]) {
        cnt++;
    }
}

return cnt;
```

Current issue: the loop updates `cnt` from adjacent array reads, but the active annotated file has no invariant. The postcondition requires `__return == array_count_transitions_spec(l)` and preservation of `IntArray::full(a, n, l)`. Without a loop invariant, symbolic execution has no durable relationship between the current counter and the prefix of `l` already scanned, and it also has no explicit record that `a` and `n` are unchanged across the loop.

Planned invariant at the `for` control point:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
    ...
}
```

The key point is that `for (i = 1; i < n; ++i)` has its invariant at the state after initialization and before the condition check. Because the precondition permits `n == 0`, a bound like `i <= n` would be false immediately after `i = 1`; the stable bound is instead `1 <= i && i <= n + 1`. The semantic part says that `cnt` is the transition count for the already covered prefix `sublist(0, i, l)`. Initially this is correct for both empty and singleton arrays because the transition count for a prefix of length at most one is zero. In a loop body with `i < n`, both `a[i]` and `a[i - 1]` are valid reads, and the branch exactly matches the recursive update from `array_count_transitions_spec(sublist(0, i, l))` to `array_count_transitions_spec(sublist(0, i + 1, l))`. After `++i`, the invariant expression again describes the next control point.

Planned loop-exit assertion immediately after the loop:

```c
/*@ Assert
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

This assertion deliberately does not claim `i == n` because the skip-loop case `n == 0` exits with `i == 1`. The assertion records only what the return witness needs: the array is still full and unchanged, and the counter equals the full-list transition specification. For `n == 0`, `sublist(0, 1, l)` is the empty list because `Zlength(l) == 0`; for `n == 1`, `sublist(0, 1, l)` is the whole singleton list; for `n > 1`, normal loop exit gives `i == n`. These cases should reduce the final bridge to list/sublist arithmetic and the Coq definition of `array_count_transitions_spec`.

## Iteration 2: Remove the loop-exit assertion after local-permission failure

Symexec result after Iteration 1 reached the function body with the corrected `--flag=value` invocation, but failed at the final return:

```text
fatal error: Error: Fail to Remove Memory Permission of i:95 in
annotated/verify_20260422_033321_array_count_transitions.c:42:4
Address found : null
```

The assertion immediately before `return cnt;` was:

```c
/*@ Assert
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

This is the symptom described in `experiences/general/ASSERTION.md`: a loop-exit assertion placed just before local-variable cleanup can interfere with removal of local permissions, especially for the local `i`. The invariant itself already preserves the full array, unchanged parameters, and the prefix semantic relation. The remaining return proof can be generated as a Coq witness from the invariant plus the negated loop condition; it does not require an extra C-level `Assert`.

Planned edit: delete only the post-loop `Assert` block and keep the loop invariant unchanged:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
    ...
}

return cnt;
```

After this edit, I will clear generated Coq files and rerun `symexec`; any remaining need to connect `sublist(0, i, l)` with `l` at exit should be handled in `proof_manual.v` as a pure list/arithmetic witness rather than by another exit assertion.
