## 2026-04-22T18:16:54+08:00 - Initial invariant for nondecreasing adjacent-pair scan

Current program point: the active annotated C file initially matches `input/is_sorted_nondecreasing.c` and has no `Inv` before the only loop:

```c
for (i = 0; i + 1 < n; ++i) {
    if (a[i] > a[i + 1]) {
        return 0;
    }
}

return 1;
```

This is a read-only scan over adjacent pairs. At the `for` loop-head control point, `i` is the left index of the next adjacent pair to inspect. Since the function returns immediately on the first descending pair, reaching the loop head means all previously inspected adjacent pairs `j` with `0 <= j < i` have satisfied `l[j] <= l[j + 1]`. The invariant therefore needs the processed-prefix fact:

```c
(forall (j: Z), (0 <= j && j < i) => l[j] <= l[j + 1])
```

The invariant must also preserve the read-only heap and unchanged parameters for the postcondition:

```c
a == a@pre &&
n == n@pre &&
IntArray::full(a, n, l)
```

The boundary condition follows the documented `for` loop rule: the invariant is checked after `i = 0` but before `i + 1 < n`. Since the precondition only gives `0 <= n`, the loop can be skipped for `n == 0` or `n == 1`. A stable loop-head bound is:

```c
0 <= i && i <= n
```

Initialization holds because `i == 0`, `0 <= n`, and the universal fact over `0 <= j < 0` is vacuous. Preservation holds because inside the body the guard gives `i + 1 < n`, and continuing past the `if (a[i] > a[i + 1])` means the current pair satisfies `l[i] <= l[i + 1]`; after `++i`, every `0 <= j < i + 1` is either an old processed pair or this current pair. The early return branch has `0 <= i && i + 1 < n && l[i] > l[i + 1]`, which directly supplies the existential witness required by the `__return == 0` postcondition.

On normal loop exit, the negated guard `!(i + 1 < n)` plus `0 <= i && i <= n` makes every postcondition index `j` satisfying `0 <= j && j + 1 < n` fall into the processed-prefix range `j < i`. Therefore the same invariant should be enough for the final `return 1` without a late loop-exit `Assert`, avoiding the known local-permission cleanup issue seen in adjacent-pair scan examples.

## 2026-04-22T18:20:00+08:00 - Strengthen loop bound for `i + 1 < n` safety without requiring `n <= INT_MAX`

The first generated `proof_manual.v` after symexec contained `proof_of_is_sorted_nondecreasing_safety_wit_2`, the VC for evaluating the loop guard expression `i + 1`. A `coqtop` probe after:

```coq
pre_process.
entailer!.
Show.
```

left this pure goal:

```coq
a_pre, n_pre, i : Z
H  : 0 <= i
H0 : i <= n_pre
H2 : 0 <= n_pre
============================
i + 1 <= 2147483647
```

The current invariant only says `i <= n`, and the formal input contract intentionally does not include `n <= INT_MAX`. Adding `n <= INT_MAX` directly to the invariant would make initialization ask for an upper bound that is not present in the pure `Require`, which is the documented pitfall for `i + 1 < n` scan loops. The reusable pattern in `experiences/general/INV.md` section 16 and `examples/array_count_increasing_steps` is to carry a source-level conditional bound instead:

```c
(0 < n => i + 1 <= n)
```

For this loop, initialization is valid: after `i = 0`, if `0 < n` then `1 <= n`. Preservation is valid: the loop body only reaches `++i` under old `i + 1 < n`; after incrementing, the new bound is old `i + 2 <= n`, which follows over integers. This conditional bound gives the safety proof enough structure while still avoiding an uninitializable `n <= INT_MAX` invariant conjunct. I will add this conjunct to the loop invariant, clear generated Coq files, and rerun `symexec`.
