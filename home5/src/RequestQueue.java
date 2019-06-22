import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;

public class RequestQueue {
    private ArrayList<PersonRequest> bq;
    private boolean stop;

    public RequestQueue() {
        bq = new ArrayList<>();
        stop = false;
    }

    public synchronized void add(PersonRequest pr) {
        bq.add(pr);
    }

    public synchronized PersonRequest getFirst() {
        if (bq.size() > 0) {
            PersonRequest p = bq.get(0);
            bq.remove(0);
            return p;
        }
        else {
            return null;
        }
    }

    public synchronized void remove(int index) {
        bq.remove(index);
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

    public synchronized PersonRequest hasEqualFrom(PersonRequest in) {
        for (PersonRequest pr : bq) {
            if (pr.getFromFloor() == in.getFromFloor()) {
                bq.remove(pr);
                return pr;
            }
        }
        return null;
    }

}
