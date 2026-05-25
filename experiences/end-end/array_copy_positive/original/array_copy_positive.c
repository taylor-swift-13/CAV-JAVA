#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_copy_positive(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((la[i] > 0 => lr[i] == la[i]) &&
           (la[i] <= 0 => lr[i] == 0))) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            out[i] = a[i];
        } else {
            out[i] = 0;
        }
    }
}
