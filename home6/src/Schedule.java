import com.oocourse.elevator3.PersonRequest;

public class Schedule implements Runnable {
    private Elevator ele;
    private RequestQueue queue;

    public Schedule(RequestQueue queue) {
        this.queue = queue;
        this.ele = new Elevator();
        Thread t = new Thread(this.ele,"ele");
        t.start();
    }

    @Override
    public void run() {
        while (true) {
            synchronized (queue) {
                if (queue.isEmpty() && queue.getStop()) {
                    break;
                }
                while (queue.isEmpty()) {
                    try {
                        queue.wait();
                        if (queue.getStop()) {
                            break;
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
                PersonRequest pr = queue.getFirst();
                if (pr != null) {
                    ele.queueadd(pr);
                    ele.setnotify();
                    ele.outadd(pr);
                    queue.notifyAll();
                }
            }
        }
        ele.setStop(true);
        ele.setnotify();
    }
}
