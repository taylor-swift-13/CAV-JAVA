#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_any_equal_sum(int n, int *a, int x, int y)
/*@ With l
    Require
      0 <= n &&
      INT_MIN <= x + y &&
      x + y <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, 0 <= i && i < n && l[i] == x + y)) ||
       (__return == 0 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != x + y))) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int target = x + y;

    for (i = 0; i < n; ++i) {
        if (a[i] == target) {
            return 1;
        }
    }

    return 0;
}
