#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (longest_increasing_run_spec : list Z -> Z) */
/*@ Import Coq Require Import longest_increasing_run */

int longest_increasing_run(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == longest_increasing_run_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cur;
    int best;

    if (n == 0) {
        return 0;
    }

    cur = 1;
    best = 1;
    for (i = 1; i < n; ++i) {
        if (a[i - 1] < a[i]) {
            cur++;
        } else {
            cur = 1;
        }
        if (best < cur) {
            best = cur;
        }
    }

    return best;
}
