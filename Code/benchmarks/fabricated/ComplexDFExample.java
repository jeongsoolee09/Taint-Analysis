class ComplexDFExample {
    
    public int f1() {
        int x1 = 1;
        return x1;
    } 

    public int f5() {
        int x51 = f1();
        int x52 = f2();
        return x51 + x52;
    }

    public void f9() {
        int x9 = f5();
    }

    public int f2() {
        int x2 = 2;
        return x2;
    }

    public int f6() {
        int x62 = f2();
        int x63 = f3();
        return x62 + x63;
    }

    public void f10() {
        int x105 = f5();
        int x106 = f6();
    }

    public int f3() {
        int x3 = 3;
        return x3;
    }

    public int f7() {
        int x7 = f3();
        return x7;
    }

    public void f11() {
        int x116 = f6();
        int x117 = f7();
    }

    public int f4() {
        int x4 = 4;
        return x4;
    }

    public int f8() {
        int x7 = f7();
        int x4 = f4();
        return x7 + x4;
    }

    public void f12() {
        int x12 = f8();
    }
}
