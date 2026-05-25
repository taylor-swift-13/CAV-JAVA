#include "../../verification_stdlib.h"

/*@ Extern Coq (lcm_simple_value: Z -> Z -> Z)
               (lcm_simple_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import lcm_simple */

int lcm_simple(int a, int b)
/*@ Require
      1 <= a &&
      1 <= b &&
      lcm_simple_value(a, b) <= INT_MAX &&
      emp
    Ensure
      lcm_simple_spec(a@pre, b@pre, __return) && emp
*/
{
    int x = a;

    while (x % b != 0) {
        x = x + a;
    }

    return x;
}
