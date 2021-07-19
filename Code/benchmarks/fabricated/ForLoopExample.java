public class ForLoopExample {
    public int intField;

    public int inc(int x) {
        for (int i=0; i<5; i++)
            x++;
        return x;
    }

    public void f() {
        int a = 1;
        int b = inc(a);
    }
}
