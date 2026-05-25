#include "../../verification_stdlib.h"

/*@ Extern Coq (count_multiples_spec : Z -> Z -> Z) */
/*@ Import Coq Require Import count_multiples */

int count_multiples(int n, int k)
/*@ Require
      1 <= n && n < INT_MAX &&
      1 <= k &&
      emp
    Ensure
      __return == count_multiples_spec(n@pre, k@pre) && emp
*/
{
    int i;
    int cnt = 0;

    for (i = 1; i <= n; ++i) {
        if (i % k == 0) {
            cnt++;
        }
    }

    return cnt;
}
