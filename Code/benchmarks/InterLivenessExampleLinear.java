package example;

public class InterLivenessExampleLinear {
    InterLivenessExampleLinear() {}

    public int example1(int c) {
        int a = 0;
        int b = a + 1;
        c = c + b;
        a = b * 2;
        return c;
    }

    public void example2(int n, int u1, int u2, int u3) {
        int i = example1(1); // example2 calls example1
        int j = n;
        int a = u1;
        i = i+1;
        j = j-1;
        a = u2;
        i = u3;
    }  

    public static void main(String[] args) {
        InterLivenessExampleLinear example = new InterLivenessExampleLinear();
        example.example2(2, 3, 4, 5);
    }
}
