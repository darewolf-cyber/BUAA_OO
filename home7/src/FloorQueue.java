import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;

public class FloorQueue<T> {
    private ConcurrentHashMap<Integer,
            CopyOnWriteArrayList<T>> queue;

    public FloorQueue() {
        queue = new ConcurrentHashMap<>();
    }

    public synchronized void add(int floor,T pr) {
        if (queue.containsKey(floor)) {
            queue.get(floor).add(pr);
        }
        else {
            CopyOnWriteArrayList<T> l =
                    new CopyOnWriteArrayList<>();
            l.add(pr);
            queue.put(floor,l);
        }
    }

    public synchronized void addAll(int floor,
                                    CopyOnWriteArrayList<T> list) {
        if (queue.containsKey(floor)) {
            queue.get(floor).addAll(list);
        }
        else {
            queue.put(floor,list);
        }
    }

    public synchronized CopyOnWriteArrayList<T> get(int floor) {
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
