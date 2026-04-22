class Abs {
    //@ requires x != Integer.MIN_VALUE;
    //@ assignable \nothing;
    //@ ensures \result >= 0;
    //@ ensures x >= 0 ==> \result == x;
    //@ ensures x < 0 ==> \result == -x;
    public static int abs(int x) {
        if (x >= 0) {
            return x;
        }
        return -x;
    }
}
