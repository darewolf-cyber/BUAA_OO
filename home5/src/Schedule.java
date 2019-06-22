import com.oocourse.elevator1.PersonRequest;

public class Schedule implements Runnable {
    private Elevator ele;
    private RequestQueue queue;

    public Schedule(RequestQueue queue) {
        this.queue = queue;
        this.ele = new Elevator();
        Thread t = new Thread(this.ele);
        t.start();
    }

    @Override
    public void run() {
        while (true) {
            synchronized (queue) {
                if (queue.isEmpty() && queue.getStop()) {
                    break;
                }
            }
            PersonRequest pr = queue.getFirst();
            if (pr != null) {
                ele.add(pr);
                PersonRequest tmp;
                while ((tmp = queue.hasEqualFrom(pr)) != null) {
                    ele.add(tmp);
                }
            }
        }
        ele.setStop(true);
    }
}
