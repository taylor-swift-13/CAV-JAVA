#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (merge_sorted_arrays_spec : list Z -> list Z -> list Z) */
/*@ Import Coq Require Import merge_sorted_arrays */

void merge_sorted_arrays(int n, int *a, int m, int *b, int *out)
/*@ With la lb lo
    Require
      0 <= n &&
      0 <= m &&
      n + m <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      Zlength(lo) == n + m &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => la[i] <= la[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < m) => lb[i] <= lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb) *
      IntArray::full(out, n + m, lo)
    Ensure
      Zlength(merge_sorted_arrays_spec(la, lb)) == n + m &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb) *
      IntArray::full(out, n + m, merge_sorted_arrays_spec(la, lb))
*/
{
    int i = 0;
    int j = 0;
    int k = 0;

    while (i < n && j < m) {
        if (a[i] <= b[j]) {
            out[k] = a[i];
            i++;
        } else {
            out[k] = b[j];
            j++;
        }
        k++;
    }

    while (i < n) {
        out[k] = a[i];
        i++;
        k++;
    }

    while (j < m) {
        out[k] = b[j];
        j++;
        k++;
    }
}
