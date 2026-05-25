#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_all_less_than_k(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] < k)) ||
       (__return == 0 &&
        (exists i, 0 <= i && i < n && l[i] >= k))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] >= k) {
            return 0;
        }
    }

    return 1;
}
