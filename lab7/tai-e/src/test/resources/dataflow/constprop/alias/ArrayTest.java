class ArrayTest {

    public static void main(String[] args) {
        loopMix();
    }

    static void loopMix() {
        int[] a = new int[5];
        for (int i = 0; i < a.length; ++i) {
            a[i] = 666;
        }
        a[4] = 777;
        int x = a[3];
        int y = a[4];
    }

}
