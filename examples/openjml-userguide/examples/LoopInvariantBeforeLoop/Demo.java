public class Demo {
  public void m() {
    int i = -1;
    //@ loop_invariant 0 <= i <= 10;
    //@ loop_decreases 10-i;
    while (i<10) i++;
  }
}
