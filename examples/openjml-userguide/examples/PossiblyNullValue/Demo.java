public class Demo {
  public static void main(String ... args) {
    /*@ nullable */ RuntimeException e = null;
    if (args.length == 0) synchronized (e) {}
    throw e;
  }
}
