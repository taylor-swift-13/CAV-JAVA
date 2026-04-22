public class Demo {
  public static void main(String ... args) {
    //@ set test(-1);
  }
  //@ model public static \bigint test(\bigint i) { return i >>> 1; }
}
