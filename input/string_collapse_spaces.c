#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_collapse_spaces_spec : list Z -> list Z) */
/*@ Import Coq Require Import string_collapse_spaces */

void string_collapse_spaces(char *s, char *out)
/*@ With l d n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, d)
    Ensure
      exists t,
        Zlength(t) == n@pre - Zlength(string_collapse_spaces_spec(l)) &&
        CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
        CharArray::full(out, n@pre + 1,
          app(app(string_collapse_spaces_spec(l), cons(0, nil)), t))
*/
{
    int i = 0;
    int j = 0;
    int in_space = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 32) {
            if (in_space == 0) {
                out[j] = 32;
                j++;
                in_space = 1;
            }
        } else {
            out[j] = s[i];
            j++;
            in_space = 0;
        }
        i++;
    }

    out[j] = 0;
}
