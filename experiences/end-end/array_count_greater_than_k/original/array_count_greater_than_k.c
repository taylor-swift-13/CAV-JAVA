#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_greater_than_k_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import array_count_greater_than_k */

int array_count_greater_than_k(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_greater_than_k_spec(l, k@pre) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cnt = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] > k) {
            cnt++;
        }
    }

    return cnt;
}
