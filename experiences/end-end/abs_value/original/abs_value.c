#include "../../verification_stdlib.h"

int abs_value(int x)
/*@ Require
      x != INT_MIN && emp
    Ensure
      __return >= 0 &&
      (__return == x@pre || __return == -x@pre) && emp
*/
{
    if (x >= 0) {
        return x;
    } else {
        return -x;
    }
}
