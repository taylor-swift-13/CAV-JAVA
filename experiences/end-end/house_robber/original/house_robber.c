#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (house_robber_spec : list Z -> Z) */
/*@ Import Coq Require Import house_robber */

int house_robber(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (0 <= l[i] && l[i] <= INT_MAX)) &&
      (forall (k: Z),
        (0 <= k && k <= n) =>
        (0 <= house_robber_spec(sublist(0, k, l)) &&
         house_robber_spec(sublist(0, k, l)) <= INT_MAX)) &&
      IntArray::full(a, n, l)
    Ensure
      __return == house_robber_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int prev2 = 0;
    int prev1 = 0;
    int take;
    int cur;

    for (i = 0; i < n; ++i) {
        take = prev2 + a[i];
        if (take > prev1) {
            cur = take;
        } else {
            cur = prev1;
        }
        prev2 = prev1;
        prev1 = cur;
    }

    return prev1;
}
