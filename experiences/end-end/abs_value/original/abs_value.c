int abs_value(int x)
/*@ Require
      x >= -2147483647 &&
      emp
    Ensure
      0 <= __return &&
      (__return == x@pre || __return == -x@pre) &&
      emp
*/
{
    if (x >= 0) {
        return x;
    } else {
        return -x;
    }
}
