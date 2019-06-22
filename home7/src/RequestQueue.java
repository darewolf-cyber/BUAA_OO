import java.util.ArrayList;

public class RequestQueue<T> {
    private ArrayList<T> bq;
    private boolean stop;

    public RequestQueue() {
        bq = new ArrayList<>();
        stop = false;
    }

    public synchronized void add(T pr) {
        bq.add(pr);
    }

    public synchronized T getFirst() {
        if (bq.size() > 0) {
            T p = bq.get(0);
            bq.remove(0);
            return p;
        }
        else {
            return null;
        }
    }

    public synchronized T first() {
        if (bq.size() > 0) {
            return bq.get(0);
        }
        else {
            return null;
        }
    }

    public synchronized void remove(int index) {
        bq.remove(index);
    }

    public synchronized void remove(Request pr) {
        bq.remove(pr);
    }

    public synchronized int size() {
        return bq.size();
    }

    public synchronized boolean isEmpty() {
        return bq.isEmpty();
    }

    public synchronized boolean getStop() {
        return stop;
    }

    public synchronized void setStop(boolean in) {
        stop = in;
    }

    @Override
    public String toString() {
        return bq.toString();
    }
}

