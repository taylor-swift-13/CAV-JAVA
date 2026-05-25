#include "../../verification_stdlib.h"

int max_of_two(int a, int b)
/*@ Require
      emp
    Ensure
      (__return == a@pre || __return == b@pre) &&
      a@pre <= __return &&
      b@pre <= __return && emp
*/
{
    if (a >= b) {
        return a;
    } else {
        return b;
    }
}
