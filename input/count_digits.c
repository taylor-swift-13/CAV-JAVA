#include "../../verification_stdlib.h"

/*@ Extern Coq (count_digits_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import count_digits */

int count_digits(int n)
/*@ Require
      0 <= n && emp
    Ensure
      count_digits_spec(n@pre, __return) && emp
*/
{
    int cnt = 0;

    if (n == 0) {
        return 1;
    }

    while (n > 0) {
        cnt++;
        n = n / 10;
    }

    return cnt;
}
