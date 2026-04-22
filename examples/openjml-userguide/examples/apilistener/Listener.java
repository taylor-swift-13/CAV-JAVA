import org.openjml.*;
import javax.tools.*;

class Listener implements DiagnosticListener<JavaFileObject> {
  @Override
  public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
    System.out.println("DIAGNOSTIC REPORTED");
    System.out.println("    Kind:           " 
                      + diagnostic.getKind());
    System.out.println("    Source:         " 
                      + diagnostic.getSource());
    System.out.println("    Start position: " 
                      + diagnostic.getStartPosition());
    System.out.println("    Position:       " 
                      + diagnostic.getPosition());
    System.out.println("    End position:   " 
                      + diagnostic.getEndPosition());
    System.out.println("    Line number:    " 
                      + diagnostic.getLineNumber());
    System.out.println("    Column number:  " 
                      + diagnostic.getColumnNumber());
    System.out.println("    Message:        " 
         + diagnostic.getMessage(java.util.Locale.getDefault()));
  }
}

