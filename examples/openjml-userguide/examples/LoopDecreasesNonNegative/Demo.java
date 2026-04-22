public class Demo {
  public void m() {
    //@ loop_invariant 0 <= j <= 10;
    //@ loop_decreases 9-j; // OK - is -1 only on loop exit
    for (int j=0; j<10; j++) {}

    //@ loop_invariant 0 <= k <= 10;
    //@ loop_decreases 10-k; // ok - best style
    for (int k=0; k<10; k++) {}

    //@ loop_invariant 0 <= i <= 10;
    //@ loop_decreases -i; // Becomes negative
    for (int i=0; i<10; i++) {}
  }
}
