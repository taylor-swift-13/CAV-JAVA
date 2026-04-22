public class Demo {
  //@ public normal_behavior
  //@   requires p >= 0;
  //@   ensures (p&1) ==  p%2;
  //@ spec_pure
  public void mod2lemma(int p) {}
  
  //@ requires k >= 0;
  //@ requires k <= Integer.MAX_VALUE/2 && k >= Integer.MIN_VALUE/2;
  public void mm(int k) {
    //@ show k;
    k = 2*k;
    //@ use mod2lemma( (k+1) );
    boolean b = ((k+1)&1) == 1;
    //@ assert b;
  }
}
