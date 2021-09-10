public class TernaryExample {
    public static void main() {
        int a = 3;
        Integer b = new Integer(1);
        Integer c = new Integer(2);
        int d = (a > 3) ? b.intValue() : c.intValue();
    }    
}
