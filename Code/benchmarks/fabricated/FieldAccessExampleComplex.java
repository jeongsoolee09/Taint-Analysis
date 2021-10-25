class X {
    int f;
    X () { this.f = 1; }
}


class Y {
    int g;
    Y () { this.g = 2; }
}


class Z {
    int h;
    Z () { this.h = 3; }
}

class FieldAccessExampleComplex {
    public static void main() {
        X x = new X();
        Y y = new Y();
        Z z = new Z();
    
        int a = 4;
        int b = 5;
        int c = 6;

        x.f = 1 + x.f;
        x.f = a + b;
        x.f = a + x.f;
        x.f = a + y.g;
        x.f = y.g;
	    x.f = y.g + z.h;
    }
}
