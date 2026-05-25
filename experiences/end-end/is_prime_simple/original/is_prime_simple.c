#include "../../verification_stdlib.h"

/*@ Extern Coq (is_prime_simple_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import is_prime_simple */

int is_prime_simple(int n)
/*@ Require
      0 <= n && emp
    Ensure
      is_prime_simple_spec(n@pre, __return) && emp
*/
{
    int d;

    if (n < 2) {
        return 0;
    }

    for (d = 2; d < n; ++d) {
        if (n % d == 0) {
            return 0;
        }
    }

    return 1;
}
