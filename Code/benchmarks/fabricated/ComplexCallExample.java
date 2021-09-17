class ComplexCallExample {
    
    public void f1() {
        int a5 = 5;
        int x1_5 = f5(a5);
        int x1_6 = f6(a5);
    } 

    public int f5(int p5) {
        int a9 = 9;
        int x5_9 = f9(a9);
        int x5_10 = f10(a9);
        return x5_9 + x5_10 + p5;
    }

    public int f9(int p9) {
        int x9 = 1;
        return x9 + p9;
    }

    public void f2() {
        int a5 = 5;
        int x2_5 = f5(a5);
        int x2_6 = f6(a5);
    }

    public int f6(int p6) {
        int a10 = 10;
        int x6_10 = f10(a10);
        int x6_11 = f11(a10);
        return x6_10 + x6_11 + p6;
    }

    public int f10(int p10) {
        int x10 = 10;
        return x10 + p10;
    }

    public void f3() {
        int a6 = 6;
        int x3_6 = f6(a6);
        int x3_7 = f7(a6);
    }

    public int f7(int p7) {
        int a11 = 11;
        int x7_11 = f7(a11);
        int x7_8 = f8(a11);
        return x7_11 + x7_8 + p7;
    }

    public int f11(int p11) {
        int x11 = 11;
        return x11 + p11;
    }

    public void f4() {
        int a8 = 8;
        int x4_8 = f8(a8);
    }

    public int f8(int p8) {
        int a12 = 12;
        int x8_12 = f12(a12);
        return x8_12 + p8;
    }

    public int f12(int p12) {
        int x12 = 12;
        return x12 + p12;
    }
}
