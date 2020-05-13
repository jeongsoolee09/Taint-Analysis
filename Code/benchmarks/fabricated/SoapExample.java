package example;

class Node {
    Node next;

    Node(Node next) {
        this.next = next;
    }

    void wrap() {
        next.next = this;
    }


    public static void main(String args[]) {
        Node a1 = new Node(null);
        Node a2 = new Node(a1);
        Node a3 = new Node(null);
        a1.next = a3;
        a2.wrap();
    }
}
