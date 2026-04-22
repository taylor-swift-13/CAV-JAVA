public class Counter {
    //@ spec_public
    private int value;

    //@ public invariant value >= 0;

    //@ ensures value == 0;
    public Counter() {
        value = 0;
    }

    //@ requires amount >= 0;
    //@ requires value <= Integer.MAX_VALUE - amount;
    //@ ensures value == \old(value) + amount;
    public void add(int amount) {
        value += amount;
    }

    //@ ensures \result == value;
    public int value() {
        return value;
    }

    public static void main(String[] args) {
        Counter counter = new Counter();
        counter.add(3);
    }
}
