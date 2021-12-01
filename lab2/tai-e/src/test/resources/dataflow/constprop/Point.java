class Point {
    public int x;
    public int y;

    int fieldNAC() {
        Point p = new Point();
        p.x = 2;
        p.y = 3;
        return p.x + p.y;
    }
}