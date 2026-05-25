#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_max(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      (exists i, 0 <= i && i < n && l[i] == __return) &&
      (forall (i: Z), (0 <= i && i < n) => l[i] <= __return) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int ret = a[0];

    for (i = 1; i < n; ++i) {
        if (a[i] > ret) {
            ret = a[i];
        }
    }

    return ret;
}
