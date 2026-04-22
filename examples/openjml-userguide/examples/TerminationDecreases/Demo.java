public class Demo {
  //@ requires i > 0;
  //@ measured_by i;
  public int test(int i) {
    return i <= 0 ? 0 : test(i);
  }
  public static void main(String ... args) { new Demo().test(10); }
}
