#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_adjacent_diff(int n, int *a, int *out)
/*@ With la lo
    Require
      1 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n - 1 &&
      (forall (i: Z),
        (0 <= i && i < n - 1) =>
        (-2147483648 <= la[i + 1] - la[i] && la[i + 1] - la[i] <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n - 1, lo)
    Ensure
      exists lr,
        Zlength(lr) == n - 1 &&
        (forall (i: Z), (0 <= i && i < n - 1) => lr[i] == la[i + 1] - la[i]) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n - 1, lr)
*/
{
    int i;

    for (i = 0; i + 1 < n; ++i) {
        out[i] = a[i + 1] - a[i];
    }
}
