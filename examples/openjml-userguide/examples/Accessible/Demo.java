//@ @org.jmlspecs.annotation.Options("--check-accessible")
public class Demo {

  public int i, j;

  //@ reads i;
  //@ pure
  public int mok() {
    return i; // OK
  }

  //@ reads \nothing;
  public int mbad() {
    return i; // ERROR
  }

  //@ reads j;
  public int mbad2() {
    return mok(); // ERROR
  }
}
