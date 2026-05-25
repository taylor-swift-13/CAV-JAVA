#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int binary_search(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != target)) ||
       (0 <= __return && __return < n &&
        l[__return] == target)) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n - 1;
    int mid;

    while (left <= right) {
        mid = left + (right - left) / 2;
        if (a[mid] == target) {
            return mid;
        }
        if (a[mid] < target) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    return -1;
}
