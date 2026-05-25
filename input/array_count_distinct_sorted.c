#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_distinct_sorted_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_distinct_sorted */

int array_count_distinct_sorted(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_distinct_sorted_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    if (n == 0) {
        return 0;
    }
    int count = 1;
    int i = 1;
    while (i < n) {
        if (a[i] != a[i - 1]) {
            count++;
        }
        i++;
    }
    return count;
}
