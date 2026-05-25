#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

char string_last_char(char *s)
/*@ With l n
    Require
      1 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == l[n - 1] &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i + 1] == 0) {
            break;
        }
        i++;
    }

    return s[i];
}
