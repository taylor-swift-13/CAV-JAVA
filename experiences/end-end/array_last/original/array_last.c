#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_last(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == l[n@pre - 1] &&
      IntArray::full(a, n@pre, l)
*/
{
    return a[n - 1];
}
