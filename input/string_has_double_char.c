#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_has_double_char(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      ((__return == 1 &&
        (exists i, 1 <= i && i < n && l[i] == l[i - 1])) ||
       (__return == 0 &&
        (forall (i: Z), (1 <= i && i < n) => l[i] != l[i - 1]))) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 1;

    if (s[0] == 0) {
        return 0;
    }

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == s[i - 1]) {
            return 1;
        }
        i++;
    }

    return 0;
}
