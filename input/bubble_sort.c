#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */

void bubble_sort(int *a, int n)
/*@ With l
    Require
      0 <= n &&
      n <= 2000 &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        (forall (i: Z) (j: Z),
          (0 <= i && i <= j && j < n) => l0[i] <= l0[j]) &&
        Permutation(l, l0) &&
        IntArray::full(a, n, l0)
*/
{
    int i, j;

    for (i = 0; i < n; ++i) {
        for (j = 0; j + 1 < n - i; ++j) {
            if (a[j] > a[j + 1]) {
                int t = a[j];
                a[j] = a[j + 1];
                a[j + 1] = t;
            }
        }
    }
}
