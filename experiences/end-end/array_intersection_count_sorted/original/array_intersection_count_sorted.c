#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_intersection_count_sorted_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import array_intersection_count_sorted */

int array_intersection_count_sorted(int n, int *a, int m, int *b)
/*@ With la lb
    Require
      0 <= n &&
      n <= INT_MAX &&
      0 <= m &&
      m <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => la[i] <= la[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < m) => lb[i] <= lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
    Ensure
      __return == array_intersection_count_sorted_spec(la, lb) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
*/
{
    int i = 0;
    int j = 0;
    int count = 0;
    while (i < n && j < m) {
        if (a[i] == b[j]) {
            count++;
            i++;
            j++;
        } else if (a[i] < b[j]) {
            i++;
        } else {
            j++;
        }
    }
    return count;
}
