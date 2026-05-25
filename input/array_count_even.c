#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_even_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_even */

int array_count_even(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_even_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cnt = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] % 2 == 0) {
            cnt++;
        }
    }

    return cnt;
}
