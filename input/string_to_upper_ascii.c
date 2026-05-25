#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_to_upper_ascii(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      exists lr,
        Zlength(lr) == n@pre &&
        (forall (i: Z),
          (0 <= i && i < n@pre) =>
          (((97 <= l[i] && l[i] <= 122) => lr[i] == l[i] - 32) &&
           ((l[i] < 97 || 122 < l[i]) => lr[i] == l[i]))) &&
        (forall (k: Z), (0 <= k && k < n@pre) => lr[k] != 0) &&
        CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] >= 97 && s[i] <= 122) {
            s[i] = s[i] - 32;
        }
        i++;
    }
}
