#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_equal(int n, int *a, int *b)
/*@ With la lb
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lb) == n &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (0 <= i && i < n) => la[i] == lb[i])) ||
       (__return == 0 &&
        (exists i, 0 <= i && i < n && la[i] != lb[i]))) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] != b[i]) {
            return 0;
        }
    }

    return 1;
}
