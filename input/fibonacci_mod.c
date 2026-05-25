#include "../../verification_stdlib.h"

/*@ Extern Coq (fib_mod_z: Z -> Z -> Z) */
/*@ Import Coq Require Import fibonacci_mod */

int fibonacci_mod(int n, int mod)
/*@ Require
      0 <= n &&
      n < 2147483647 &&
      0 < mod &&
      mod <= 1073741824 &&
      emp
    Ensure
      __return == fib_mod_z(n@pre, mod@pre) && emp
*/
{
    int i;
    int a = 0;
    int b = 1 % mod;
    int c;

    if (n == 0) {
        return 0;
    }

    for (i = 2; i <= n; ++i) {
        c = (a + b) % mod;
        a = b;
        b = c;
    }

    return b;
}
