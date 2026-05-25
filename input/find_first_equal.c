#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int find_first_equal(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != k)) ||
       (0 <= __return && __return < n &&
        l[__return] == k &&
        (forall (i: Z), (0 <= i && i < __return) => l[i] != k))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            return i;
        }
    }

    return -1;
}
