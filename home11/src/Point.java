import javafx.util.Pair;

public class Point implements Comparable<Point> {
    private Pair<Integer,Integer> pair;
    private Integer dist;

    public Point(Pair<Integer, Integer> pair, Integer dist) {
        this.pair = pair;
        this.dist = dist;
    }

    public Pair<Integer, Integer> getPair() {
        return pair;
    }

    public int getDist() {
        return dist;
    }

    @Override
    public int compareTo(Point o) {
        return dist.compareTo(o.getDist());
    }

}
