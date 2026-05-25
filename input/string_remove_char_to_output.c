#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_remove_char_to_output_spec : list Z -> Z -> list Z) */
/*@ Import Coq Require Import string_remove_char_to_output */

int string_remove_char_to_output(char *s, char *out, char c)
/*@ With l d n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, d)
    Ensure
      exists t,
        __return == Zlength(string_remove_char_to_output_spec(l, c@pre)) &&
        Zlength(t) == n@pre - Zlength(string_remove_char_to_output_spec(l, c@pre)) &&
        CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
        CharArray::full(out, n@pre + 1,
          app(app(string_remove_char_to_output_spec(l, c@pre), cons(0, nil)), t))
*/
{
    int i = 0;
    int j = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] != c) {
            out[j] = s[i];
            j++;
        }
        i++;
    }

    out[j] = 0;
    return j;
}
