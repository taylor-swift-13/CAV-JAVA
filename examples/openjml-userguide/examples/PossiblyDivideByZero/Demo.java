public class Demo {
  //@ requires i != 0;
  public void mok(int i) {
    int k = 1/i;
  }
  public void mbad(int i) {
    int k = 1/i;
  }
}
