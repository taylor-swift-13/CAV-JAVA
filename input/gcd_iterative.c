#include "../../verification_stdlib.h"

/*@ Extern Coq (gcd_iterative_spec : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import gcd_iterative */

int gcd_iterative(int a, int b)
/*@ Require
      0 <= a &&
      0 <= b &&
      0 < a + b &&
      emp
    Ensure
      gcd_iterative_spec(a@pre, b@pre, __return) && emp
*/
{
    int r;

    while (b != 0) {
        r = a % b;
        a = b;
        b = r;
    }

    return a;
}
