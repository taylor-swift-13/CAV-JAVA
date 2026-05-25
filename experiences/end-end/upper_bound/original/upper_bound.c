#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int upper_bound(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      IntArray::full(a, n, l)
    Ensure
      0 <= __return && __return <= n &&
      (forall (i: Z), (0 <= i && i < __return) => l[i] <= target) &&
      ((__return == n) ||
       (__return < n && l[__return] > target)) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n;
    int mid;

    while (left < right) {
        mid = left + (right - left) / 2;
        if (a[mid] <= target) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    return left;
}
