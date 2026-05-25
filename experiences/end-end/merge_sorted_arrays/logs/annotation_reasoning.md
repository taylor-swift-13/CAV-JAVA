## 2026-04-22 19:58 CST - Initial merge loop invariants

Current program point: the active annotated file `annotated/verify_20260422_194235_merge_sorted_arrays.c` currently has no loop invariants. The three loops are:

```c
while (i < n && j < m) { ... out[k] = ...; ... k++; }
while (i < n) { out[k] = a[i]; i++; k++; }
while (j < m) { out[k] = b[j]; j++; k++; }
```

Without `Inv` annotations, symbolic execution has no stable state for the partially written `out` array. The output heap changes after every write, so the invariant must describe the current `out` contents as a completed prefix plus the untouched suffix from the original logical list `lo`.

Planned main-loop invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= j && j <= m &&
      k == i + j &&
      0 <= k && k <= n + m &&
      a == a@pre && b == b@pre && out == out@pre &&
      n == n@pre && m == m@pre &&
      n + m <= INT_MAX &&
      Zlength(la) == n && Zlength(lb) == m && Zlength(lo) == n + m &&
      sortedness facts for la/lb using Znth &&
      cross-boundary ordering facts &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb) *
      IntArray::full(out, n + m,
        app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
            sublist(k, n + m, lo)))
*/
while (i < n && j < m) { ... }
```

Initialization: before the first guard check, `i == 0`, `j == 0`, and `k == 0`. The merged prefix is `merge_sorted_arrays_spec(nil, nil)`, which is empty, so `app(nil, sublist(0, n + m, lo))` matches the original `IntArray::full(out, n + m, lo)` from the precondition. The input arrays are read-only and remain `IntArray::full(a, n, la)` and `IntArray::full(b, m, lb)`.

Preservation: in a body iteration, the guard gives `i < n` and `j < m`, so both `a[i]` and `b[j]` are readable. If `a[i] <= b[j]`, the C code writes `a[i]` to `out[k]` and increments `i`; the Coq merge specification chooses the head of the remaining `a` side under the same tie rule. If `a[i] > b[j]`, the code writes `b[j]` and increments `j`; the Coq merge specification chooses the head of `b`. The cross-boundary facts retained in the invariant are the reusable history needed for pure proof obligations that show the old merged prefix extended by the selected element equals the merge of the newly consumed prefixes. The output heap suffix moves from `sublist(k, n + m, lo)` to `sublist(k + 1, n + m, lo)` after the write and `k++`.

Exit usability: when the main loop exits, the invariant plus the negated guard gives `i == n || j == m`. The following tail loops need this phase fact. If `i < n` in the second loop, then necessarily `j == m`; if the second loop exits, then `i == n`. The third loop then copies any remaining `b` suffix. At final exit, the invariant state has `i == n`, `j == m`, and `k == n + m`, so the output heap becomes:

```c
IntArray::full(out, n + m,
  app(merge_sorted_arrays_spec(sublist(0, n, la), sublist(0, m, lb)),
      sublist(n + m, n + m, lo)))
```

With the input length facts, this normalizes to the required `IntArray::full(out, n + m, merge_sorted_arrays_spec(la, lb))`. I will add the tail-loop invariants with the same semantic output-prefix shape, plus the phase facts `i == n || j == m`, `(i < n) => j == m`, and finally `i == n` for the third loop.

## 2026-04-22 19:46 CST - Include bridge for active annotated file

The first `symexec` run did not reach annotation checking. It failed during preprocessing:

```text
fatal error: No such file ../verification_stdlib.h in search path in QCP_examples/CAV/annotated/verify_20260422_194235_merge_sorted_arrays.c:1:35
```

The active annotated file lives in `QCP_examples/CAV/annotated/`, so the copied input includes need to point two levels up to `QCP_examples/`. Existing successful active annotated files use this form:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

I changed only the active annotated copy to that include depth. This does not alter the contract or program semantics; it only lets the verify front end parse the same headers from the annotated-file location.

## 2026-04-22 19:48 CST - Remove unsupported phase disjunction from second loop invariant

After fixing the includes, `symexec` reached the transition from the main loop to the second loop and failed at the invariant on `while (i < n)`:

```text
Partial Solve Invariant Error in ...verify_20260422_194235_merge_sorted_arrays.c:108:4
```

The failing path was the valid main-loop exit where `j >= m` and `i < n`. The left side contained:

```text
j_149_value >= m_90_pre;
i_150_value < n_96_pre;
0 <= j_149_value;
j_149_value <= m_90_pre;
```

The target generated from my second-loop invariant incorrectly required:

```text
i_210_value == n_96_pre
```

This came from writing the phase fact as a disjunction:

```c
(i == n || j == m) &&
((i < n) => j == m) &&
```

The front end split/selected the disjunction in a way that made the `i == n` case mandatory at this loop head, which is false exactly when the second loop should run. The second loop body only needs the implication `i < n => j == m`; on a body iteration the guard supplies `i < n`, so this recovers `j == m`. On a skipped second loop path, the implication is enough and the third loop entry can later derive `i == n` from the second loop's negated guard plus `i <= n`.

I changed the second-loop invariant to remove the disjunction and keep only:

```c
0 <= i && i <= n &&
0 <= j && j <= m &&
((i < n) => j == m) &&
k == i + j &&
...
```

This should initialize on both main-loop exits: if `i < n`, the negated main guard and bounds force `j == m`; if `i == n`, the implication is vacuous.

## 2026-04-22 19:53 CST - Simplify merge invariant shape after CPU-bound symexec

After removing the disjunction, the next `symexec` run stayed CPU-bound for several minutes and `logs/qcp_run.log` contained only:

```text
symexec_start=2026-04-22 19:47:23 +0800
```

No parser, strategy, or function-entry output was flushed. This matches the `SYMEXEC.md` warning for complex merge invariants: the key semantics may be right, but nested quantified implications can make the front end stall before useful VC generation.

The previous invariant carried two cross-boundary quantified facts in every loop:

```c
(forall (bi: Z) (ai: Z),
  (0 <= bi && bi < j && i <= ai && ai < n) =>
    Znth(bi, lb, 0) < Znth(ai, la, 0)) &&
(forall (ai: Z) (bi: Z),
  (0 <= ai && ai < i && j <= bi && bi < m) =>
    Znth(ai, la, 0) <= Znth(bi, lb, 0)) &&
```

I am replacing these front-end-heavy history facts with a single semantic decomposition equality and an explicit prefix-length fact:

```c
Zlength(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb))) == k &&
merge_sorted_arrays_spec(la, lb) ==
  app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
      merge_sorted_arrays_spec(sublist(i, n, la), sublist(j, m, lb))) &&
```

The heap shape remains:

```c
IntArray::full(out, n + m,
  app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
      sublist(k, n + m, lo)))
```

This keeps exactly the information needed by the return witness: the written prefix is the first part of the full merge result, the unwritten suffix is still old `lo`, and `k` is the prefix length. The difficult proof that the C branch preserves the decomposition now becomes a pure merge/list theorem in `proof_manual.v`, which is preferable to blocking VC generation.

## 2026-04-22 19:59 CST - Replace recursive decomposition with existential output prefix

The semantic decomposition equality also timed out under a 240-second shell `timeout`; `logs/qcp_run.log` ended with:

```text
symexec_status=124
```

The likely remaining front-end cost is the recursive `merge_sorted_arrays_spec` equality inside the invariant:

```c
merge_sorted_arrays_spec(la, lb) ==
  app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
      merge_sorted_arrays_spec(sublist(i, n, la), sublist(j, m, lb)))
```

I changed the invariant shape again so the heap is described by an existential concrete written prefix rather than by a recursive merge expression:

```c
/*@ Inv exists ldone,
      ...
      Zlength(ldone) == k &&
      (forall (p: Z),
        (0 <= p && p < k) =>
          Znth(p, ldone, 0) == Znth(p, merge_sorted_arrays_spec(la, lb), 0)) &&
      IntArray::full(out, n + m,
        app(ldone, sublist(k, n + m, lo)))
*/
```

This is intentionally more operational. The symbolic executor only needs to track that the updated heap extends `ldone` by one cell and shrinks the old suffix. The proof phase will still have to show that the element written at index `k` is the `k`-th element of `merge_sorted_arrays_spec(la, lb)` and that a full-length `ldone` equal elementwise to the final spec can be collapsed to the postcondition list.

## 2026-04-22 20:01 CST - Reduce output prefix to direct final-spec sublist

The existential-prefix invariant also timed out after 120 seconds:

```text
symexec_status=124
```

The likely issue is that the quantified elementwise relation still appears in every loop invariant:

```c
(forall (p: Z),
  (0 <= p && p < k) =>
    Znth(p, ldone, 0) == Znth(p, merge_sorted_arrays_spec(la, lb), 0)) &&
```

I replaced that with the smallest heap expression that still connects directly to the postcondition:

```c
IntArray::full(out, n + m,
  app(sublist(0, k, merge_sorted_arrays_spec(la, lb)),
      sublist(k, n + m, lo)))
```

The scalar invariant still keeps `k == i + j` and the phase facts. This annotation no longer tries to expose the merge-prefix proof structure to the front end; instead, each write will generate pure obligations showing that the selected C value is exactly the next element of the final merge specification.

## 2026-04-22 20:05 CST - Restore VC-generating merge-prefix invariant from archived same-function workspace

Current blocker: the active annotated file `annotated/verify_20260422_194235_merge_sorted_arrays.c` now uses this output heap in all three loop invariants:

```c
IntArray::full(out, n + m,
  app(sublist(0, k, merge_sorted_arrays_spec(la, lb)),
      sublist(k, n + m, lo)))
```

The latest `symexec` run timed out before VC generation:

```text
symexec_start=2026-04-22 20:01:00 +0800
symexec_end=2026-04-22 20:03:00 +0800
symexec_status=124
```

and the generated files `merge_sorted_arrays_goal.v`, `merge_sorted_arrays_proof_auto.v`, `merge_sorted_arrays_proof_manual.v`, and `merge_sorted_arrays_goal_check.v` are all zero bytes. This means the current annotation shape is not usable for proof.

The archive `./archieve/examples_backup_20260422_011624/merge_sorted_arrays/` is directly applicable: its `original/merge_sorted_arrays.v` is identical to the current `input/merge_sorted_arrays.v`, and its C contract differs only by include depth. That archived workspace has non-empty generated VCs, so its active annotation is concrete evidence of a better `symexec` shape.

I will replace the current final-spec-sublist heap shape with the archived prefix-list shape:

```c
/*@ Inv exists lout_done,
      ...
      Zlength(lout_done) == k &&
      lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)) &&
      IntArray::full(out, n + m,
        app(lout_done, sublist(k, n + m, lo)))
*/
```

This keeps the recursive merge spec out of the heap list argument except through the existential prefix equality. Initialization chooses `lout_done = nil`, so the output predicate becomes `IntArray::full(out, n + m, app(nil, sublist(0, n + m, lo)))`, matching the original output ownership after list normalization. Preservation after a write extends `lout_done` by one element and shrinks the old suffix from `sublist(k, n + m, lo)` to `sublist(k + 1, n + m, lo)`. Return usability is restored because when the third loop exits, `i == n`, `j == m`, and `k == n + m`, so `lout_done` equals `merge_sorted_arrays_spec(sublist(0, n, la), sublist(0, m, lb))` and the suffix is empty.

I will also restore the two cross-boundary history facts from the archived successful annotation:

```c
(forall (bp: Z) (ai: Z),
  (0 <= bp && bp < j && i <= ai && ai < n) =>
    Znth(bp, lb, 0) < Znth(ai, la, 0)) &&
(forall (ap: Z) (bi: Z),
  (0 <= ap && ap < i && j <= bi && bi < m) =>
    Znth(ap, la, 0) <= Znth(bi, lb, 0)) &&
```

These facts are necessary for the merge-prefix proof obligations: when the code selects `a[i]`, previously consumed `b` elements must be strictly less than future `a` elements because the spec chooses `a` on ties; when the code selects `b[j]`, consumed `a` elements must be less-or-equal to future `b` elements. The facts use explicit `Znth(index, list, 0)` rather than bracket notation because prior logs show bracket notation in quantified ghost-list facts caused frontend type and size inference failures.

For the second tail loop, I will use the archived `Inv Assert exists lout_done` shape and preserve `(i == n || j == m)` instead of only `((i < n) => j == m)`. This loop invariant is checked at the loop head before the guard is consumed, so both main-loop exit paths must satisfy it. For the third tail loop, the second-loop exit plus bounds justify strengthening to `i == n`, and the archived invariant uses `k == n + j` to make the final `k == n + m` derivation direct.
