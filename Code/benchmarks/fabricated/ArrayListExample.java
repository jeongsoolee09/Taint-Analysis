import java.util.ArrayList;

class ArrayListExample {


  public void adder(ArrayList<Integer> lst) {
    lst.add(5);
    lst.add(6);
    lst.add(7);
    lst.add(8);
  }

  public void foo() {
    ArrayList<Integer> list = new ArrayList();

    int a = 1;
    int b = 2;
    int c = 3;

    adder(list);

    list.add(a);
    list.add(b);
    list.add(c);
  }
}
