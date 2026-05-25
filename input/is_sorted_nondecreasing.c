#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int is_sorted_nondecreasing(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1])) ||
       (__return == 0 &&
        (exists i, 0 <= i && i + 1 < n && l[i] > l[i + 1]))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 0; i + 1 < n; ++i) {
        if (a[i] > a[i + 1]) {
            return 0;
        }
    }

    return 1;
}
