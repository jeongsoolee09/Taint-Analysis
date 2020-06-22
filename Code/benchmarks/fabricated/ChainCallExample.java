public class ChainCallExample {

    public int intfield;
    ChainCallExample() {
        this.intfield = 1;
    }

    public int f1(int u) {
        return u-3;
    }

    public int f2(int x) {
        return x++;
    }

    public int f3(int y) {
        return y--;
    }

    public int f4(int z) {
        return z*2;
    }

    public static void main() {
        ChainCallExample ch = new ChainCallExample();
        int i = ch.intfield;
        int a = ch.f1(i);
        int b = ch.f2(a);
        int c = ch.f3(b);
        int d = ch.f4(c);
    }
}