import com.oocourse.elevator3.PersonRequest;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;

public class FloorQueue {
    private ConcurrentHashMap<Integer,
            CopyOnWriteArrayList<PersonRequest>> queue;

    public FloorQueue() {
        queue = new ConcurrentHashMap<>();
    }

    public synchronized void add(int floor,PersonRequest pr) {
        if (queue.containsKey(floor)) {
            queue.get(floor).add(pr);
        }
        else {
            CopyOnWriteArrayList<PersonRequest> l =
                    new CopyOnWriteArrayList<>();
            l.add(pr);
            queue.put(floor,l);
        }
    }

    public synchronized void addAll(int floor,
                                    CopyOnWriteArrayList<PersonRequest> list) {
        if (queue.containsKey(floor)) {
            queue.get(floor).addAll(list);
        }
        else {
            queue.put(floor,list);
        }
    }

    public synchronized CopyOnWriteArrayList<PersonRequest> get(int floor) {
        return queue.get(floor);
    }

    public synchronized boolean containsKey(int floor) {
        return queue.containsKey(floor);
    }

    public synchronized void remove(int index) {
        queue.remove(index);
    }

    public synchronized int size() {
        return queue.keySet().size();
    }

    public synchronized boolean isEmpty() {
        return queue.isEmpty();
    }

    public String toString() {
        return queue.toString();
    }
}
