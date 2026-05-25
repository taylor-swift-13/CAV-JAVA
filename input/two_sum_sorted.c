#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int two_sum_sorted(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i < j && j < n) =>
          INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX) &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, exists j,
          0 <= i && i < j && j < n && l[i] + l[j] == target)) ||
       (__return == 0 &&
        (forall (i: Z) (j: Z),
          (0 <= i && i < j && j < n) => l[i] + l[j] != target))) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n - 1;
    int s;

    while (left < right) {
        s = a[left] + a[right];
        if (s == target) {
            return 1;
        }
        if (s < target) {
            left++;
        } else {
            right--;
        }
    }

    return 0;
}
