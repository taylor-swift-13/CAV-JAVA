public class Demo {

  public static void test(/*@ nullable */ Object o) {
    //@ ghost \TYPE t = \typeof(o);
  }

  public static void tp(/*@ nullable */ Object o) { m(o); }

  public static void m(/*@ non_null */ Object o) { }

}
