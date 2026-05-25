#include "../../verification_stdlib.h"

/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
{
    int i;
    int res = 1;

    for (i = 1; i <= n; ++i) {
        res = res * i;
    }

    return res;
}
