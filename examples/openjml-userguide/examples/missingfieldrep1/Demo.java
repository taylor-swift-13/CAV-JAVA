public class Demo {

  //@ model public int modelField;
  //@ represents modelField = 42;

  public static void main(String... args) { 
     Demo d = new Demo();
     //@ show d.modelField;
  }

}
