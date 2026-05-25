#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_last_positive(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] <= 0)) ||
       (0 <= __return && __return < n &&
        l[__return] > 0 &&
        (forall (i: Z), (__return < i && i < n) => l[i] <= 0))) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int ans = -1;

    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            ans = i;
        }
    }

    return ans;
}
