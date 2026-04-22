import java.io.*;
import org.openjml.IAPI;
public class Run {
  public static void main(String... args) {
    PrintWriter pw = new PrintWriter(System.out);
    int ex = -1;
    try {
      ex = IAPI.openjml("--esc", "A.java");
      System.out.println("EXIT: " + ex);
      ex = IAPI.openjml("--rac", "A.java");
      System.out.println("EXIT: " + ex);
      IAPI api = IAPI.make();
      ex = api.execute("--check", "B.java");
      System.out.println("EXIT: " + ex);
      if (ex != IAPI.OK) System.out.println("Exit not OK");
    } finally {
      pw.close();
    }
  }
}

