#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_second_largest(int n, int *a)
/*@ With l
    Require
      2 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i < j && j < n) => l[i] != l[j]) &&
      IntArray::full(a, n, l)
    Ensure
      exists top second,
        0 <= top && top < n &&
        0 <= second && second < n &&
        top != second &&
        l[second] == __return &&
        l[top] > __return &&
        (forall (i: Z),
          (0 <= i && i < n && i != top) => l[i] <= __return) &&
        IntArray::full(a, n, l)
*/
{
    int i;
    int max1 = a[0];
    int max2 = a[1];

    if (max2 > max1) {
        int t = max1;
        max1 = max2;
        max2 = t;
    }

    for (i = 2; i < n; ++i) {
        if (a[i] > max1) {
            max2 = max1;
            max1 = a[i];
        } else if (a[i] > max2) {
            max2 = a[i];
        }
    }

    return max2;
}
