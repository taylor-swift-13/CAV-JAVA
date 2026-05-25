#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_find_char(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      ((__return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != c)) ||
       (0 <= __return && __return < n &&
        l[__return] == c &&
        (forall (i: Z), (0 <= i && i < __return) => l[i] != c))) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == c) {
            return i;
        }
        i++;
    }

    return -1;
}
