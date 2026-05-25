#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (max_subarray_sum_spec : list Z -> Z) */
/*@ Import Coq Require Import max_subarray_sum */

int max_subarray_sum(int n, int *a)
/*@ With l
    Require
      1 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (lo: Z), (forall (hi: Z),
        (0 <= lo && lo < hi && hi <= n) =>
        (INT_MIN <= sum(sublist(lo, hi, l)) &&
         sum(sublist(lo, hi, l)) <= INT_MAX))) &&
      IntArray::full(a, n, l)
    Ensure
      __return == max_subarray_sum_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cur = a[0];
    int best = a[0];

    for (i = 1; i < n; ++i) {
        if (cur + a[i] < a[i]) {
            cur = a[i];
        } else {
            cur = cur + a[i];
        }
        if (best < cur) {
            best = cur;
        }
    }

    return best;
}
