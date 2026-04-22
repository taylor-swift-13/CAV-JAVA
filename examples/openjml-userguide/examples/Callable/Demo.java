public class Demo {
  //@ callable \nothing;
  public static void test1() {}
  //@ callable \nothing;
  public static void test2() {}
  //@ callable test2;
  public static void main(String ... args ) { test1(); }
}
  
