#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_has_adjacent_equal(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, 1 <= i && i < n && l[i] == l[i - 1])) ||
       (__return == 0 &&
        (forall (i: Z), (1 <= i && i < n) => l[i] != l[i - 1]))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 1; i < n; ++i) {
        if (a[i] == a[i - 1]) {
            return 1;
        }
    }

    return 0;
}
