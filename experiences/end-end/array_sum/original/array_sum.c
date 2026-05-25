#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_sum(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= 10000 &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i < n) => (-10000 <= l[i] && l[i] <= 10000)) &&
      -2147483648 <= sum(l) && sum(l) <= 2147483647 &&
      IntArray::full(a, n, l)
    Ensure
      __return == sum(l) && IntArray::full(a, n, l)
*/
{
    int i;
    int ret = 0;

    for (i = 0; i < n; ++i) {
        ret += a[i];
    }

    return ret;
}
