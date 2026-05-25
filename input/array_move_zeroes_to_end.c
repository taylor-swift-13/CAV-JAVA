#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_move_zeroes_to_end_spec : list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */

void array_move_zeroes_to_end(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      Zlength(array_move_zeroes_to_end_spec(l)) == n@pre &&
      IntArray::full(a, n@pre, array_move_zeroes_to_end_spec(l))
*/
{
    int write = 0;
    int i = 0;

    while (i < n) {
        if (a[i] != 0) {
            a[write] = a[i];
            write++;
        }
        i++;
    }

    while (write < n) {
        a[write] = 0;
        write++;
    }
}
