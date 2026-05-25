#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_zero_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_zero */

int array_count_zero(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_zero_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int count = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] == 0) {
            count++;
        }
    }

    return count;
}
