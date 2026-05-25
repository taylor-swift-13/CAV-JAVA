#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_first_peak(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == -1 &&
        (forall (i: Z),
          (0 < i && i + 1 < n) =>
          (l[i] < l[i - 1] || l[i] < l[i + 1]))) ||
       (0 < __return && __return + 1 < n &&
        l[__return] >= l[__return - 1] &&
        l[__return] >= l[__return + 1] &&
        (forall (i: Z),
          (0 < i && i < __return) =>
          (l[i] < l[i - 1] || l[i] < l[i + 1])))) &&
      IntArray::full(a, n, l)
*/
{
    int i = 1;

    while (i + 1 < n) {
        if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
            return i;
        }
        i++;
    }

    return -1;
}
