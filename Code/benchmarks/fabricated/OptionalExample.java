import java.util.OptionalInt;

class OptionalExample {
    public static int add(int a, int b) {
        int out = a+b;
        return out;
    }

    public static void main() {
        OptionalInt x = OptionalInt.of(1);
        int y = 2;
        int rest = OptionalExample.add(x.getAsInt(), y);
    }
}
