#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void copy_array(int n, int *src, int *dst)
/*@ With ls ld
    Require
      0 <= n &&
      Zlength(ls) == n &&
      Zlength(ld) == n &&
      IntArray::full(src, n, ls) *
      IntArray::full(dst, n, ld)
    Ensure
      IntArray::full(src, n, ls) *
      IntArray::full(dst, n, ls)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        dst[i] = src[i];
    }
}
