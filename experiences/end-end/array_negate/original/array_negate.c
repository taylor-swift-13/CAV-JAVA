#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void array_negate(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (-2147483648 <= -la[i] && -la[i] <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == -la[i]) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        out[i] = -a[i];
    }
}
