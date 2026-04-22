public class Demo {
  public int i;
  public int j;
  //@ writable i if j > 0;
  public void test() {
    j = 0;
    i = 1;
  }
  public static void main(String ... args) { new Demo().test(); }
}
