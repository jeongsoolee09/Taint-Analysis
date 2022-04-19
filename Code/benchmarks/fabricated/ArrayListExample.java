import java.util.ArrayList;

class ArrayListExample {


  public void adder(ArrayList<Integer> lst) {
    lst.add(5);
    lst.add(6);
    lst.add(7);
    lst.add(8);
  }

  public void foo() {
    ArrayList<Integer> list = new ArrayList<Integer>();

    adder(list);

    list.add(1);
    list.add(2);
    list.add(3);
  }
}
