import java.util.Arrays;

class LambdaExample {
    LambdaExample() {
    }

    public static int[] transform(int[] a) {
        return Arrays.stream(a)
            .map(num -> num+1)
	    .filter(num2 -> num2 % 2 == 0)
            .toArray();
    }

    public static void main() {
        int[] x = {1, 2, 3};
        LambdaExample.transform(x);
    }
}
