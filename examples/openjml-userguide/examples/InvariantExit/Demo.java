public class Demo {
  public int i = 0;
  //@ public invariant i >= 0;
  public void test() {
    i = -1;
  }
}
