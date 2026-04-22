public class Demo {
  public static void main(String ... args) {
    int i = 0;
    //@ loop_invariant 0 <= i <= 10;
    //@ loop_decreases 10 - i;
    while ( i++ < 10 ) {}
    System.out.println("END " + i);
  }
}
