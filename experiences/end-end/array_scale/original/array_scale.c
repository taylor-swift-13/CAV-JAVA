#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void array_scale(int n, int *a, int k, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (-2147483648 <= la[i] * k && la[i] * k <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == la[i] * k) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        out[i] = a[i] * k;
    }
}
