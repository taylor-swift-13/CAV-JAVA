int add_two(int a, int b)
/*@ Require
      -2147483648 <= a + b && a + b <= 2147483647 && emp
    Ensure
      __return == a@pre + b@pre && emp
*/
{
    return a + b;
}
