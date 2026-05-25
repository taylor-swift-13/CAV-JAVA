#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_is_palindrome(int n, char *s)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      CharArray::full(s, n, l)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] == l[n - 1 - i])) ||
       (__return == 0 &&
        (exists i, 0 <= i && i < n && l[i] != l[n - 1 - i]))) &&
      CharArray::full(s, n, l)
*/
{
    int left = 0;
    int right = n - 1;

    while (left < right) {
        if (s[left] != s[right]) {
            return 0;
        }
        left++;
        right--;
    }

    return 1;
}
