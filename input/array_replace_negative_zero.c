#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_replace_negative_zero(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        Zlength(l0) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((l[i] < 0 => l0[i] == 0) &&
           (l[i] >= 0 => l0[i] == l[i]))) &&
        IntArray::full(a, n, l0)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            a[i] = 0;
        }
    }
}
