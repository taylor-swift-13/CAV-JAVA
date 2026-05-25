#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_swap_ends(int n, int *a)
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
          ((n < 2 => l0[i] == l[i]) &&
           (n >= 2 =>
             ((i == 0 => l0[i] == l[n - 1]) &&
              (i == n - 1 => l0[i] == l[0]) &&
              (i != 0 && i != n - 1 => l0[i] == l[i]))))) &&
        IntArray::full(a, n, l0)
*/
{
    int t;

    if (n < 2) {
        return;
    }

    t = a[0];
    a[0] = a[n - 1];
    a[n - 1] = t;
}
