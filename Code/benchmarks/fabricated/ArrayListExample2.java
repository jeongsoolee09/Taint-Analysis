import java.util.ArrayList;

class ArrayListExample2 {
    public ArrayList<Integer> adder(ArrayList<Integer> lst) {
        lst.add(5);
        lst.add(6);
        lst.add(7);
        lst.add(8);

        return lst;
    }

    public void foo() {
        ArrayList<Integer> list = new ArrayList<Integer>();

        list.add(1);
        list.add(2);
        list.add(3);

        ArrayList<Integer> list2 = adder(list);
        
        list2.add(9);
        list2.add(10);
    }

}
