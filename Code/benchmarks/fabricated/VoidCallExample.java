public class VoidCallExample {
  private class InnerClass {
    InnerClass() { }
    private void goo(int a) {
      System.out.println(a);
      System.out.println(a);
      System.out.println(a);
    }
  }

  public InnerClass innerObject;

  public void foo() {
    int a = 1;
    innerObject.goo(a);
    System.out.println(a);
    System.out.println(a);
    System.out.println(a);
  }
}
