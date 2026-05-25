#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_starts_with(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      ((n == 0 && c == 0 && __return == 1) ||
       (n == 0 && c != 0 && __return == 0) ||
       (0 < n && l[0] == c && __return == 1) ||
       (0 < n && l[0] != c && __return == 0)) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    if (s[0] == c) {
        return 1;
    }
    return 0;
}
