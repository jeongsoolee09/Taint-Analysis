import java.util.Arrays;

class LambdaExample {
    LambdaExample() {
    }

    public static int[] transform(int[] a) {
        int[] out = Arrays.stream(a)
            .map(num -> num+1)
	    .filter(num2 -> num2 % 2 == 0)
            .toArray();
        return out;
    }

    public static void main() {
        int[] x = {1, 2, 3};
        LambdaExample.transform(x);
    }
}
