#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_copy_prefix(int k, char *src, char *dst)
/*@ With l d n
    Require
      0 <= k && k <= n && n < INT_MAX &&
      Zlength(l) == n &&
      Zlength(d) == k + 1 &&
      (forall (i: Z), (0 <= i && i < n) => l[i] != 0) &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, k + 1, d)
    Ensure
      CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, k@pre + 1,
        app(sublist(0, k@pre, l), cons(0, nil)))
*/
{
    int i;

    for (i = 0; i < k; ++i) {
        dst[i] = src[i];
    }
    dst[k] = 0;
}
