public class Demo {
  int i;
  int j;
  //@ readable i if j > 0;
  public int test() {
    return i;
  }
  public static void main(String ... args) { new Demo().test(); }
}
