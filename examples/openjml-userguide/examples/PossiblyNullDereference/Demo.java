public class Demo {
  int i;
  public static int test(/*@ nullable */ Demo d) {
    return d.i;
  }
  public static void main(String ... args) { test(null); }
}
