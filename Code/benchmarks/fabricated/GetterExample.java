class MyStruct {
    private int x;
    private String y;
    
    MyStruct() {
        this.x = 1;
        this.y = "hihi";
    }
    
    public int getX() {
        return this.x;
    }

    public String getY() {
        return this.y;
    }
}

class GetterExample {
    public static void main() {
        MyStruct myStruct = new MyStruct();
        int a = myStruct.getX();
        String b = myStruct.getY();
    }
}
