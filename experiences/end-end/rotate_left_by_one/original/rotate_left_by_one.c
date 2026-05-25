#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void rotate_left_by_one(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((i < n - 1 => lr[i] == l[i + 1]) &&
           (i == n - 1 => lr[i] == l[0]))) &&
        IntArray::full(a, n, lr)
*/
{
    int i;
    int first = a[0];

    for (i = 0; i < n - 1; ++i) {
        a[i] = a[i + 1];
    }
    a[n - 1] = first;
}
