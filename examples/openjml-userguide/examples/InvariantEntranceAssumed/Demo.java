public class Demo {
  public static void main(String... args) {
    i = 1;
    test();
  }
  public static void test() {
    i = 0;
  }
  public static int i = 0;
  //@ public static invariant i == 0;
}
