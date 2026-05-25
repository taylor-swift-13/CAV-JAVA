#include "../../verification_stdlib.h"

/*@ Extern Coq (tribonacci_z: Z -> Z) */
/*@ Import Coq Require Import tribonacci */

int tribonacci(int n)
/*@ Require
      0 <= n && n <= 37 && emp
    Ensure
      __return == tribonacci_z(n@pre) && emp
*/
{
    int i;
    int a = 0;
    int b = 1;
    int c = 1;
    int d;

    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 1;
    }

    for (i = 3; i <= n; ++i) {
        d = a + b + c;
        a = b;
        b = c;
        c = d;
    }

    return c;
}
