## Annotation iteration 1

Program point: the single `for (i = 0; i < n; ++i)` loop in `reverse_copy`.

Unannotated code:

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[n - 1 - i];
}
```

The contract requires `src` to stay equal to the original logical list `ls` and `dst` to become `rev(ls)`. At the loop test point, `i` is the number of already copied elements. The written prefix of `dst` should therefore be the reverse of the suffix of `ls` already consumed from the right:

```c
rev(sublist(n@pre - i, n@pre, ls))
```

The unwritten suffix of `dst` still has its original values:

```c
sublist(i, n@pre, ld)
```

The invariant will keep the full source array unchanged and model `dst` as:

```c
IntArray::full(dst, n@pre,
  app(rev(sublist(n@pre - i, n@pre, ls)), sublist(i, n@pre, ld)))
```

Initialization: after `i = 0`, the written prefix is `rev(sublist(n, n, ls))`, which is empty, and the suffix is `sublist(0, n, ld)`, so the destination is still `ld`.

Preservation: under `i < n`, the assignment writes `src[n - 1 - i]`, which is the next element immediately before the already consumed source suffix. After the `for` increment, the written prefix should become `rev(sublist(n - (i + 1), n, ls))`, and the destination suffix should become `sublist(i + 1, n, ld)`.

Exit: when the loop condition is false, the invariant gives `i == n` from `0 <= i <= n` and `!(i < n)`. The destination list then becomes `app(rev(sublist(0, n, ls)), sublist(n, n, ld))`, which should simplify to `rev(ls)` using `Zlength(ls) == n`.

Added invariant:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      src == src@pre &&
      dst == dst@pre &&
      n == n@pre &&
      Zlength(ls) == n@pre &&
      Zlength(ld) == n@pre &&
      IntArray::full(src, n@pre, ls) *
      IntArray::full(dst, n@pre,
        app(rev(sublist(n@pre - i, n@pre, ls)), sublist(i, n@pre, ld)))
*/
```

## Annotation iteration 2

The first `symexec` run did not reach annotation checking. It failed during preprocessing with:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_212943_reverse_copy.c:1:35
```

The active annotated file was copied from `input/reverse_copy.c` and still used:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

Existing top-level active annotated files in this repository use `../../...` includes, for example `annotated/verify_20260422_133747_copy_array.c`. This is a Verify-workspace preprocessing fix only; it does not change the function contract or implementation. The next edit changes the active annotated copy to:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```
