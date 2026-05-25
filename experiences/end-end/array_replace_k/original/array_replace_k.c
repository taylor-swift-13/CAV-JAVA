#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_replace_k(int n, int *a, int old_k, int new_k)
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
          ((l[i] == old_k => l0[i] == new_k) &&
           (l[i] != old_k => l0[i] == l[i]))) &&
        IntArray::full(a, n, l0)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] == old_k) {
            a[i] = new_k;
        }
    }
}
