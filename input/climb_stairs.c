#include "../../verification_stdlib.h"

/*@ Extern Coq (climb_stairs_z: Z -> Z) */
/*@ Import Coq Require Import climb_stairs */

int climb_stairs(int n)
/*@ Require
      0 <= n && n <= 45 && emp
    Ensure
      __return == climb_stairs_z(n@pre) && emp
*/
{
    if (n <= 1) {
        return 1;
    }

    int prev2 = 1;
    int prev1 = 1;
    int cur = 0;

    for (int i = 2; i <= n; i++) {
        cur = prev1 + prev2;
        prev2 = prev1;
        prev1 = cur;
    }

    return cur;
}
