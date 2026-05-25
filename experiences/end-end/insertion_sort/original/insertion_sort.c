#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (insertion_sort_spec : list Z -> list Z -> Prop) */
/*@ Import Coq Require Import insertion_sort */

void insertion_sort(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        Zlength(lr) == n@pre &&
        insertion_sort_spec(l, lr) &&
        IntArray::full(a, n@pre, lr)
*/
{
    int i;
    int j;
    int key;

    for (i = 1; i < n; ++i) {
        key = a[i];
        j = i - 1;
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = key;
    }
}
