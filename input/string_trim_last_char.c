#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_trim_last_char(int n, char *s)
/*@ With l
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      exists lr,
        Zlength(lr) == n@pre + 1 &&
        ((n@pre == 0 &&
          lr == app(l, cons(0, nil))) ||
         (0 < n@pre &&
          (forall (i: Z), (0 <= i && i < n@pre - 1) => lr[i] == l[i]) &&
          lr[n@pre - 1] == 0 &&
          lr[n@pre] == 0)) &&
        CharArray::full(s, n@pre + 1, lr)
*/
{
    if (n > 0) {
        s[n - 1] = 0;
    }
}
