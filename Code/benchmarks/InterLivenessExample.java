package example;

public class InterLivenessExample {
    InterLivenessExample() {}

    public int example1(int c) {
        int a = 0;
        do {
            int b = a + 1;
            c = c + b;
            a = b * 2;
        } while (a < 20);    // not in the example, made it up

        return c;
    }

    public void example2(int n, int u1, int u2, int u3) {
        int i = example1(1); // example2 calls example1
        int j = n;
        int a = u1;
        while (i < 10) {     // not in the example, made it up
            i = i+1;
            j = j-1;
            if (j > 0)       // not in the example, made it up
                a = u2;
            else 
                i = u3;
        }
    }

    public static void main(String[] args) {
        InterLivenessExample example = new InterLivenessExample();
        example.example2(2, 3, 4, 5);
    }
}
