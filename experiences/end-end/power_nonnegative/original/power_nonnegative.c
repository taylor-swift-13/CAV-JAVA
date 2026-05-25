#include "../../verification_stdlib.h"

/*@ Extern Coq (power_nonnegative_z: Z -> Z -> Z) */
/*@ Import Coq Require Import power_nonnegative */

int power_nonnegative(int base, int exp)
/*@ Require
      0 <= exp &&
      (forall (k: Z), (0 <= k && k <= exp) =>
        (INT_MIN <= power_nonnegative_z(base, k) &&
         power_nonnegative_z(base, k) <= INT_MAX)) &&
      emp
    Ensure
      __return == power_nonnegative_z(base@pre, exp@pre) && emp
*/
{
    int i;
    int ans = 1;

    for (i = 0; i < exp; ++i) {
        ans = ans * base;
    }

    return ans;
}
