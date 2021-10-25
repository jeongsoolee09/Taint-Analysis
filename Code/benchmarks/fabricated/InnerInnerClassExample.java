class InnerInnerClassExample {
  private int a5;
  private int a6;
  private InnerClass b2;

  class InnerClass {
    private int a3;
    private int a4;
    private InnerInnerClass b1;

    class InnerInnerClass {
      private int a1;
      private int a2;

      InnerInnerClass(int x1, int x2) {
        this.a1 = x1;
        this.a2 = x2;
      }

    }
    InnerClass(int x3, int x4) {
      this.a3 = x3;
      this.a4 = x4;
      int x = 1;
      int y = 2;
      this.b1 = new InnerInnerClass(x, y);
    }
  }
  InnerInnerClassExample(int x5, int x6) {
    this.a5 = x5;
    this.a6 = x6;
    int x = 3;
    int y = 4;
    this.b2 = new InnerClass(x, y);
  }
} 
