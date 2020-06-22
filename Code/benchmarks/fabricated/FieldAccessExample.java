public class FieldAccessExample {

    public int intField;
    public FieldAccessExample fld;

    FieldAccessExample () {
        this.intField = 1;
        this.fld = null;
    }

    public static void main() {
        FieldAccessExample x = new FieldAccessExample();
        FieldAccessExample z = new FieldAccessExample();
        int y = 2;
        x.fld = z;
        x.fld.intField = y;
    }
}