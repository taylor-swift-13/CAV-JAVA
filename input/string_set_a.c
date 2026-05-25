#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_set_a(int n, char *s)
/*@ With l
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n + 1 &&
      CharArray::full(s, n + 1, l)
    Ensure
      exists lr,
        Zlength(lr) == n + 1 &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == 97) &&
        lr[n] == 0 &&
        CharArray::full(s, n + 1, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        s[i] = 97;
    }
    s[n] = 0;
}
