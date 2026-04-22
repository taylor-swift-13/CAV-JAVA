//CMD: openjml --esc T_Feasibility3a.java
public class T_Feasibility3a {

  //@ requires i >= 0;
  public void m(int i) {
    int j = abs(i);
    //@ show i, j;
    if (i != j) {
      // Should never get here!
      //@ unreachable
    }
  }

  //@ requires i != Integer.MIN_VALUE;
  //@ ensures \result >= 0 && (\result == i || \result == -i);
  //@ pure
  public static int abs(int i) {
    return i < 0 ? -i : i;
  }
}
