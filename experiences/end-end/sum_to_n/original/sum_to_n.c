#include "../../verification_stdlib.h"

int sum_to_n(int n)
/*@ Require
      0 <= n &&
      INT_MIN <= n * (n + 1) / 2 &&
      n * (n + 1) / 2 <= INT_MAX &&
      emp
    Ensure
      __return == n@pre * (n@pre + 1) / 2 && emp
*/
{
    int i;
    int ret = 0;

    for (i = 1; i <= n; ++i) {
        ret += i;
    }

    return ret;
}
