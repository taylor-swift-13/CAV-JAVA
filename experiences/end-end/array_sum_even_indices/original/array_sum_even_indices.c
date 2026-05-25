#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_sum_even_indices_spec : list Z -> Z) */
/*@ Import Coq Require Import array_sum_even_indices */

int array_sum_even_indices(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (INT_MIN <= l[i] && l[i] <= INT_MAX)) &&
      (forall (k: Z),
        (0 <= k && k <= n) =>
        (INT_MIN <= array_sum_even_indices_spec(sublist(0, k, l)) &&
         array_sum_even_indices_spec(sublist(0, k, l)) <= INT_MAX)) &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_sum_even_indices_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int sum = 0;

    for (i = 0; i < n; ++i) {
        if (i % 2 == 0) {
            sum += a[i];
        }
    }

    return sum;
}
