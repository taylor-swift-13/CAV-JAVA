#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_fill_char(int n, char c, char *s)
/*@ With l
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n + 1 &&
      CharArray::full(s, n + 1, l)
    Ensure
      exists lr,
        Zlength(lr) == n + 1 &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == c) &&
        lr[n] == 0 &&
        CharArray::full(s, n + 1, lr)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        s[i] = c;
    }
    s[n] = 0;
}
