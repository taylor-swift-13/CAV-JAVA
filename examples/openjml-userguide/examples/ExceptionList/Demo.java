public class Demo {
  //@ signals_only NullPointerException;
  public static void test() throws Exception {
    throw new java.io.FileNotFoundException();
  }
  public static void main(String ... args) throws Exception { test(); }
}
