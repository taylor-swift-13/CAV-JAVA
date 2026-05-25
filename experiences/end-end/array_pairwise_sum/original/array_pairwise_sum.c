#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void array_pairwise_sum(int n, int *a, int *b, int *out)
/*@ With la lb lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lb) == n &&
      Zlength(lo) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (-2147483648 <= la[i] + lb[i] && la[i] + lb[i] <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == la[i] + lb[i]) &&
        IntArray::full(a, n, la) *
        IntArray::full(b, n, lb) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        out[i] = a[i] + b[i];
    }
}
