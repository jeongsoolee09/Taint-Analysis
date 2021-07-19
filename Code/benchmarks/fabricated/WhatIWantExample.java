public class WhatIWantExample {

    WhatIWantExample() {}

    public int m1() {
        return 1;
    }

    public int m2(int u1) {
        return ++u1;
    }

    public void m3(int u2) {
        System.out.println(u2);
    }

    public void f() {
        int x = m1();
        g(x);
    }

    public void g(int y) {
        int z = m2(y);
        h(z);
    }

    public void h(int w) {
        m3(w);
    }

    public static void main() {
        WhatIWantExample w = new WhatIWantExample();
        w.f();
    }
}
