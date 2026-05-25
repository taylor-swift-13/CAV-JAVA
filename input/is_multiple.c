#include "../../verification_stdlib.h"

int is_multiple(int a, int b)
/*@ Require
      0 < b && emp
    Ensure
      ((__return == 1 &&
        (exists q, a@pre == q * b@pre)) ||
       (__return == 0 &&
        (forall (q: Z), a@pre != q * b@pre))) &&
      emp
*/
{
    if (a % b == 0) {
        return 1;
    }
    return 0;
}
