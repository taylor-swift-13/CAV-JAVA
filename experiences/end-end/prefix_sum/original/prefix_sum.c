#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void prefix_sum(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      (forall (k: Z),
        (0 <= k && k <= n) =>
        (INT_MIN <= sum(sublist(0, k, la)) &&
         sum(sublist(0, k, la)) <= INT_MAX)) &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          lr[i] == sum(sublist(0, i + 1, la))) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;
    int acc = 0;

    for (i = 0; i < n; ++i) {
        acc += a[i];
        out[i] = acc;
    }
}
