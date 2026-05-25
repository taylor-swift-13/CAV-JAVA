#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */

void selection_sort(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        Zlength(lr) == n@pre &&
        (forall (i: Z) (j: Z),
          (0 <= i && i <= j && j < n@pre) => lr[i] <= lr[j]) &&
        Permutation(l, lr) &&
        IntArray::full(a, n@pre, lr)
*/
{
    int i;
    int j;
    int min_idx;
    int tmp;

    for (i = 0; i < n; ++i) {
        min_idx = i;
        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_idx]) {
                min_idx = j;
            }
        }
        tmp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = tmp;
    }
}
