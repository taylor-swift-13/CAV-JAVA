public class Demo {
  public static Integer test1() {
    return null;
  }
  public static void test2() {
    test1();
    //@ reachable
  }
  public static void main(String ... args) { test2(); }
}
