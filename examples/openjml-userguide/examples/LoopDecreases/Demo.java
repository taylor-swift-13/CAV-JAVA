public class Demo {
  public void m() {
    //@ loop_invariant 0 <= i <= 10;
    //@ loop_decreases i; // Does not decrease
    for (int i=0; i<10; i++) {}

    //@ loop_invariant 0 <= k <= 10;
    //@ loop_decreases 10-k; // OK - decreases
    for (int k=0; k<10; k++) {}
  }
}
