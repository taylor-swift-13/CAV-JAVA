#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */

int partition_nonnegative(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        0 <= __return &&
        __return <= n@pre &&
        Zlength(lr) == n@pre &&
        (forall (k: Z), (0 <= k && k < __return) => lr[k] < 0) &&
        (forall (k: Z), (__return <= k && k < n@pre) => lr[k] >= 0) &&
        Permutation(l, lr) &&
        IntArray::full(a, n@pre, lr)
*/
{
    int i = 0;
    int j = n - 1;
    int tmp;

    while (i <= j) {
        if (a[i] < 0) {
            i++;
        } else {
            tmp = a[i];
            a[i] = a[j];
            a[j] = tmp;
            j--;
        }
    }

    return i;
}
