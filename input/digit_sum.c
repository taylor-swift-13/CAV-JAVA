#include "../../verification_stdlib.h"

/*@ Extern Coq (digit_sum_z : Z -> Z) */
/*@ Import Coq Require Import digit_sum */

int digit_sum(int n)
/*@ Require
      0 <= n && emp
    Ensure
      __return == digit_sum_z(n@pre) && emp
*/
{
    int sum = 0;

    while (n > 0) {
        sum += n % 10;
        n = n / 10;
    }

    return sum;
}
