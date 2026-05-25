#include "../../verification_stdlib.h"

int add_two(int a, int b)
/*@ Require
      INT_MIN <= a + b &&
      a + b <= INT_MAX && emp
    Ensure
      __return == a@pre + b@pre && emp
*/
{
    return a + b;
}
