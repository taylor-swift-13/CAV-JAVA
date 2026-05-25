# Annotation reasoning

## Initial loop invariant for two-pointer palindrome scan

Current annotated file before this edit has no loop invariant:

```c
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
```

This is insufficient for `symexec` because the `while (left < right)` loop reads `s[left]` and `s[right]`, returns early on a mismatch, and otherwise moves both pointers. The postcondition needs either a concrete mismatch index for return `0`, or a universal symmetric equality for return `1`. Without an invariant, the generated VCs would have no persistent fact describing which symmetric pairs have already been checked or how `right` relates to `left`.

Planned invariant at the real while control point:

```c
/*@ Inv Assert
      0 <= left && left <= n &&
      right == n - 1 - left &&
      -1 <= right && right < n &&
      n == n@pre &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < left) => l[k] == l[n - 1 - k]) &&
      CharArray::full(s, n, l)
*/
while (left < right) {
```

The bounds make both array reads legal under the loop guard: if `left < right`, then `0 <= left`, `right < n`, and `right` is nonnegative because `left >= 0` and `left < right`. The equation `right == n - 1 - left` is initialized by `left = 0; right = n - 1;` and preserved by the paired updates `left++` and `right--`. The quantified fact records exactly the already-checked prefix: for every processed index `k < left`, the symmetric pair in the original list matches.

Initialization is valid because `left == 0`, so the quantified prefix is empty, and `right == n - 1`. For `n == 0`, `right == -1`, the bounds still hold and the loop is skipped. Preservation is valid because in a non-returning iteration, `s[left] == s[right]`; with `right == n - 1 - left` and unchanged `CharArray::full(s, n, l)`, this supplies the new checked pair when `left` becomes `left + 1`. Exit is useful because `left >= right` and `right == n - 1 - left` imply every unprocessed index has a mirror in the processed prefix or is the middle element, so the universal palindrome postcondition can be completed with arithmetic and symmetry. The mismatch branch can use witness `i = left`, since the guard and invariant give `0 <= left < n` and `n - 1 - left == right`.
