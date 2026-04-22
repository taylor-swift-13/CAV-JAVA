public class Demo {

  //@ ensures \result >= 0;
  static int mm(int i) {
    return i;
  }

  public static void main(String ... args) { mm(-1); }
}
