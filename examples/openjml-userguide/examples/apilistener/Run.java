import org.openjml.*;
import javax.tools.*;

public class Run {

  public static void main(String... args) {
    try {
      IAPI api = IAPI.make(null, new Listener());
      int x = api.execute("--esc","--progress","-jmltesting","A.java");
      System.exit(x);
    } catch (Exception e) {
      System.out.println("Exception: " + e);
    }
  }
}

