public class FieldAccessExample {

    private int intField;
    private FieldAccessExample fld;
    private boolean yeeyee;
    private Integer yee;
    private double yoyo;

    FieldAccessExample () {
        this.intField = 1;
        this.fld = null;
        this.yeeyee = true;
        this.yee = new Integer(1);
        this.yoyo = 3.14;
    }

    public static void main() {
        FieldAccessExample x = new FieldAccessExample();
        FieldAccessExample z = new FieldAccessExample();
        int y = 2;
        x.fld = z;
        x.fld.intField = y;
    }
}
