#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_prefix_max(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n@pre &&
        (forall (i: Z),
          (0 <= i && i < n@pre) =>
          (exists j,
            0 <= j && j <= i &&
            lr[i] == la[j]) &&
          (forall (k: Z),
            (0 <= k && k <= i) =>
            la[k] <= lr[i])) &&
        IntArray::full(a, n@pre, la) *
        IntArray::full(out, n@pre, lr)
*/
{
    int i;
    int cur;

    if (n == 0) {
        return;
    }

    cur = a[0];
    out[0] = cur;
    for (i = 1; i < n; ++i) {
        if (a[i] > cur) {
            cur = a[i];
        }
        out[i] = cur;
    }
}
