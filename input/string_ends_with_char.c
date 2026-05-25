#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_ends_with_char(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      ((n == 0 && __return == 0) ||
       (0 < n && l[n - 1] == c && __return == 1) ||
       (0 < n && l[n - 1] != c && __return == 0)) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    if (s[0] == 0) {
        return 0;
    }

    while (1) {
        if (s[i + 1] == 0) {
            break;
        }
        i++;
    }

    if (s[i] == c) {
        return 1;
    }
    return 0;
}
