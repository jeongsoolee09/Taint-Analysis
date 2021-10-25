class FieldAccessExampleComplex {
    public static void main() {
        int[] f = {1};
        int[] g = {2};
        int[] h = {3};

        int a = 4;
        int b = 5;
        int c = 6;

        f[0] = 1 + f[0];
        f[0] = a + b;
        f[0] = a + f[0];
        f[0] = a + g[0];
        f[0] = g[0];
	    f[0] = g[0] + h[0];
    }
}
