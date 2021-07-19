public class ObjectFlowing {

    public Integer source() {
        Integer x = new Integer(1);
        return x;
    }

    public Integer foo() {
        Integer o = source();
        return o;
    }

    public void sink(int integer2) {
        System.out.println(integer2);
    }

    public void goo() {
        Integer o2 = foo();
        int integer = o2.intValue();
        sink(integer);
    }

}
