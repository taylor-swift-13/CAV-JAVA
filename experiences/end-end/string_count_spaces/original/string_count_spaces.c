#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_count_spaces_spec : list Z -> Z) */
/*@ Import Coq Require Import string_count_spaces */

int string_count_spaces(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == string_count_spaces_spec(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int cnt = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 32) {
            cnt++;
        }
        i++;
    }

    return cnt;
}
