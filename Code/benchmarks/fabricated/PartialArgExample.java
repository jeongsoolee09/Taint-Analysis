public class PartialArgExample {
    PartialArgExample() {}
  
    public void printWrapper3(int x, int y, int z) {
        System.out.println(x);
    }
  
    public void printWrapper1(int x) {
        System.out.println(x);
    }

    public void argProvider() {
        int a = 1;
        int b = 2;
        int c = 3;
        printWrapper3(3+2+1, 2, c);
        // printWrapper1(a);
    }
  
    public static void main() {
        PartialArgExample p = new PartialArgExample();
        p.argProvider();
    }
}
