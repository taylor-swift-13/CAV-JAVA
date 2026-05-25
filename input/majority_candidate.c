#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (majority_candidate_spec : list Z -> Z) */
/*@ Import Coq Require Import majority_candidate */

int majority_candidate(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int candidate = a[0];
    int count = 1;

    for (i = 1; i < n; ++i) {
        if (count == 0) {
            candidate = a[i];
            count = 1;
        } else if (a[i] == candidate) {
            count++;
        } else {
            count--;
        }
    }

    return candidate;
}
