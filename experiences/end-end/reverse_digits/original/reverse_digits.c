#include "../../verification_stdlib.h"

/*@ Extern Coq (reverse_digits_z : Z -> Z) */
/*@ Import Coq Require Import reverse_digits */

int reverse_digits(int n)
/*@ Require
      0 <= n &&
      0 <= reverse_digits_z(n) &&
      reverse_digits_z(n) <= INT_MAX && emp
    Ensure
      __return == reverse_digits_z(n@pre) && emp
*/
{
    int ans = 0;

    while (n > 0) {
        ans = ans * 10 + n % 10;
        n = n / 10;
    }

    return ans;
}
