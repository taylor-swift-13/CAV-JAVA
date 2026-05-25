#include "../../verification_stdlib.h"

/*@ Extern Coq (count_divisors_spec : Z -> Z) */
/*@ Import Coq Require Import count_divisors */

int count_divisors(int n)
/*@ Require
      1 <= n && n < INT_MAX && emp
    Ensure
      __return == count_divisors_spec(n@pre) && emp
*/
{
    int d;
    int cnt = 0;

    for (d = 1; d <= n; ++d) {
        if (n % d == 0) {
            cnt++;
        }
    }

    return cnt;
}
