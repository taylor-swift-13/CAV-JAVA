## 2026-04-22 annotation plan before first edit

Current C code:

```c
int i;
int acc = 0;

for (i = 0; i < n; ++i) {
    acc += a[i];
    out[i] = acc;
}
```

The loop head is the `for` control point after `i = 0` and before checking `i < n`. At that point `i` is the number of output cells already written, so the accumulator should describe the already processed prefix:

```c
acc == sum(sublist(0, i, la))
```

The input array must remain unchanged and available for later reads and for the final postcondition:

```c
IntArray::full(a, n@pre, la)
```

The output array should be split into a written prefix and the original untouched suffix. I will use existential lists `l1` and `l2`, with `l1` carrying the semantic prefix-sum facts and `l2` carrying the still-unwritten original suffix:

```c
exists l1 l2,
  Zlength(l1) == i &&
  Zlength(l2) == n@pre - i &&
  (forall (k: Z), (0 <= k && k < i) =>
     l1[k] == sum(sublist(0, k + 1, la))) &&
  (forall (k: Z), (0 <= k && k < n@pre - i) =>
     l2[k] == lo[i + k]) &&
  IntArray::full(out, n@pre, app(l1, l2))
```

Initialization should hold with `i == 0`, `acc == 0`, `l1 == nil`, and `l2 == lo`; this matches `sum(sublist(0, 0, la))`. Preservation should hold because the body first changes `acc` from `sum(sublist(0, i, la))` to `sum(sublist(0, i + 1, la))` by adding `a[i]`, then writes exactly that value to `out[i]`. The precondition's quantified prefix-sum range fact includes `k == i + 1`, so the addition result is in signed-int range when `0 <= i < n`. On exit, `i == n` and `l2` has length `0`, so `app(l1, l2)` can serve as the postcondition witness `lr`; the invariant already gives all per-index prefix-sum facts for `0 <= k < n`.

The body needs a bridge assertion before `acc += a[i]` to expose `data_at(a + i * sizeof(int), int, la[i])`, and another bridge before `out[i] = acc` to expose the `out` cell at index `i`. After the write, a final bridge rebuilds `IntArray::full(out, n@pre, app(l1', sublist(i + 1, n@pre, lo)))` for the next loop head.

## 2026-04-22 include path fix before second symexec

The first `symexec` run failed before parsing the function body:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_210632_prefix_sum.c:1:35
symexec_status=1
```

This is a front-end include search-path issue in the active annotated copy, not an invariant failure. The verified examples under `CAV/examples/*/annotated/*.c` use includes relative to `QualifiedCProgramming/QCP_examples`, for example:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

The next edit changes only the active annotated copy's three include directives from `../...` to `../../...`. The loop invariant and body bridge assertions are unchanged, so after this fix I will rerun `symexec` from a clean `coq/generated` directory and interpret any later failure as an annotation or proof issue rather than a file path issue.

## 2026-04-22 remove in-body bridge assertions that drop local scalar state

After fixing the include paths, `symexec` reached the loop body but failed at the compound assignment:

```text
fatal error: Cannot derive the precondition of Memory Read. in annotated/verify_20260422_210632_prefix_sum.c:73:8
symexec_status=1
```

The failing annotated region was:

```c
/*@ exists l1 l2,
      ...
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
    which implies
      IntArray::missing_i(a, i, 0, n@pre, la) *
      data_at(a + (i * sizeof(int)), int, la[i]) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
acc += a[i];
```

This bridge exposes the `a[i]` array cell, but it also replaces the current symbolic state with a narrow separation assertion that does not mention the local scalar store for `acc`. A compound assignment must both read `a[i]` and read/write `acc`; with `acc` dropped from the bridge target, symbolic execution cannot derive the memory-read precondition for the statement. This matches the earlier `array_scale` issue where an in-body bridge exposed array cells but lost scalar `k`, and the stable fix was to remove the bridge and let normal symbolic execution handle array reads/writes from the full array predicate.

The next edit removes all three in-body bridge assertions around `acc += a[i]` and `out[i] = acc`. The invariant remains:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      acc == sum(sublist(0, i, la)) &&
      ...
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
```

This still expresses the full loop-head state. For the body, the verifier can derive the read of `a[i]` from `IntArray::full(a, n@pre, la)` and the write to `out[i]` from `IntArray::full(out, n@pre, app(l1, l2))`; after the two statements, the invariant preservation obligation should become a pure list/arithmetic proof about extending `l1` with `sum(sublist(0, i + 1, la))`.
