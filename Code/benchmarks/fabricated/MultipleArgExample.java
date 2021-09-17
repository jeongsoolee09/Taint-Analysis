class MultipleArgExample {

    public int add(int x, int y, int z) {
        return x+y+z;
    }

    public void foo() {
        int a = 1;
        int b = 2;
        int c = 3;
        int d = add(a, b, c);
    }
}
