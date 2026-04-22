public class Demo {
  //@ requires b;
  public void test(boolean b) {
    if (b) {
    } else {
      //@ reachable
    }
  }
}
