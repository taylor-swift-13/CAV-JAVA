public class Demo {
  public static void main(String... args) {
    test();
    i = 0;
  }
  public static void test() {
    i = 1;
  }
  public static int i = 0;
  //@ public static invariant i == 0;
}
