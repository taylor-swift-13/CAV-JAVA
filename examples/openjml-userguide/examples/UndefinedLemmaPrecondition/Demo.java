public class Demo {
  //@ public normal_behavior
  //@   requires p >= 0;
  //@   ensures (p&1) ==  p%2;
  //@ spec_pure
  public void mod2lemma(int p) {}
  
  //@ requires k <= Integer.MAX_VALUE/2 && k >= -1; // The -1 just so the counterexample is always the same
  public void m(int k) {
  //@ show k;
  k = 2*k;
  //@ use mod2lemma( (k+1) );
  boolean b = ((k+1)&1) == 1; // Error expected when k is -1
  //@ assert b;
  }
  public static void main(String ... args) { (new Demo()).m(-1); }
}
