#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_transitions_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_transitions */

int array_count_transitions(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_transitions_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cnt = 0;

    for (i = 1; i < n; ++i) {
        if (a[i] != a[i - 1]) {
            cnt++;
        }
    }

    return cnt;
}
