#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_equal(char *a, char *b)
/*@ With la lb na nb
    Require
      0 <= na && na < INT_MAX &&
      0 <= nb && nb < INT_MAX &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      (forall (k: Z), (0 <= k && k < na) => la[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nb) => lb[k] != 0) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
    Ensure
      ((__return == 1 &&
        na == nb &&
        (forall (k: Z), (0 <= k && k < na) => la[k] == lb[k])) ||
       (__return == 0 &&
        (na != nb ||
         (exists k, 0 <= k && k < na && k < nb && la[k] != lb[k])))) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (a[i] == 0) {
            break;
        }
        if (b[i] == 0) {
            break;
        }
        if (a[i] != b[i]) {
            return 0;
        }
        i++;
    }

    if (a[i] == 0 && b[i] == 0) {
        return 1;
    }
    return 0;
}
