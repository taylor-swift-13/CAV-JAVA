#include "../../verification_stdlib.h"

int min_of_three(int a, int b, int c)
/*@ Require
      emp
    Ensure
      (__return == a@pre || __return == b@pre || __return == c@pre) &&
      __return <= a@pre &&
      __return <= b@pre &&
      __return <= c@pre && emp
*/
{
    int m = a;

    if (b < m) {
        m = b;
    }
    if (c < m) {
        m = c;
    }

    return m;
}
