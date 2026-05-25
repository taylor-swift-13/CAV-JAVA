#include "../../verification_stdlib.h"

/*@ Extern Coq (fib_z: Z -> Z) */
/*@ Import Coq Require Import fibonacci */

int fibonacci(int n)
/*@ Require
      0 <= n && n <= 46 && emp
    Ensure
      __return == fib_z(n@pre) && emp
*/
{
    int i;
    int a = 0;
    int b = 1;
    int c;

    if (n == 0) {
        return 0;
    }

    for (i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }

    return b;
}
