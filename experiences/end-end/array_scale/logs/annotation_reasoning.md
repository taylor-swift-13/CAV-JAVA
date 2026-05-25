## Annotation iteration 1: prefix/suffix invariant for array_scale

Current source fragment before this annotation change:

```c
int i;

for (i = 0; i < n; ++i) {
    out[i] = a[i] * k;
}
```

The loop writes one output cell per iteration and never modifies the input array `a`, the pointer values, `n`, or the scalar multiplier `k`. The postcondition needs a final list `lr` of length `n` such that every element satisfies `lr[t] == la[t] * k`. At the loop head, `i` is the next index to process, so the stable loop shape should describe:

- `0 <= i <= n@pre`;
- unchanged parameters `a == a@pre`, `out == out@pre`, `n == n@pre`, and `k == k@pre`;
- a written output prefix `l1` of length `i`, where `l1[t] == la[t] * k@pre`;
- an unwritten output suffix `l2` of length `n@pre - i`, where `l2[t] == lo[i + t]`;
- the heap as `IntArray::full(a, n@pre, la) * IntArray::full(out, n@pre, app(l1, l2))`.

Initialization holds with `i == 0`, an empty `l1`, and `l2 == lo`. Preservation holds because one iteration reads `a[i] == la[i]`, reads the current output cell from the original suffix value `lo[i]`, writes `la[i] * k@pre`, and then rebuilds the output list as an extended prefix plus `sublist(i + 1, n@pre, lo)`. Exit is useful because when the loop condition is false, the invariant and `i <= n@pre` give `i == n@pre`, so the suffix has length zero and the full output list is exactly the completed result prefix.

The bridge assertion before the assignment will expose `data_at(a + i*sizeof(int), int, la[i])` and `data_at(out + i*sizeof(int), int, lo[i])` from the full arrays. The bridge assertion after the assignment will rebuild the full output array with an existential `l1'` of length `i + 1` satisfying the completed-prefix relation. This mirrors the already verified `array_add` pattern, replacing `la[i] + lb[i]` with `la[i] * k@pre`.

## Annotation iteration 2: active annotated include paths

The first `symexec` run did not reach VC generation. It failed at file parsing:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_080741_array_scale.c:1:35
```

Current annotated include fragment:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

This is not a contract or loop-invariant failure. The active verified examples in this repository use `../../verification_stdlib.h`, `../../verification_list.h`, and `../../int_array_def.h` in the active annotated copy. The next edit changes only the active annotated file's include directives to match that established layout, then reruns `symexec` from a clean generated directory. The loop invariant and bridge assertions remain unchanged.

## Annotation iteration 3: remove bridge assertions that drop scalar `k`

After fixing the include paths, `symexec` reached the assignment but failed at the post-assignment `which implies` on line 63 of the active annotated file. The diagnostic showed the just-written output cell as:

```text
store ( (out_83_pre + (i_128_value * (Size_of signed int))) , ((la_95_free[i_128_value]) * NULL) , signed int )
```

The expected assertion needed:

```text
store (..., ((la_95_free[i_128_value]) * k_86_pre), signed int)
```

This means the bridge before the assignment exposed the array cells but did not preserve the scalar local storage for `k`, so evaluating `a[i] * k` after the bridge lost the multiplier value. Close scalar examples such as `array_count_greater_than_k` and array update examples such as `array_negate` keep scalar equalities in the invariant and do not force an in-body `which implies` bridge for the statement. The next edit removes the two in-body bridge assertions while keeping the loop invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      k == k@pre &&
      ...
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
for (i = 0; i < n; ++i) {
    out[i] = a[i] * k;
}
```

The invariant still gives initialization, preservation, and exit information. This change avoids a too-narrow bridge state that loses scalar locals and lets symbolic execution use the verifier's normal array read/write rules for the assignment.
