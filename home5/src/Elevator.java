import com.oocourse.TimableOutput;
import com.oocourse.elevator1.PersonRequest;

import java.util.Comparator;
import java.util.PriorityQueue;

public class Elevator implements Runnable {
    private RequestQueue queue;
    private int curFloor;
    private int direction;
    private int state;

    public Elevator() {
        this.curFloor = 1;
        this.direction = 0;
        this.queue = new RequestQueue();
    }

    public synchronized void add(PersonRequest pr) {
        queue.add(pr);
    }

    public synchronized PersonRequest getFirst() {
        return queue.getFirst();
    }

    public synchronized void setStop(boolean in) {
        queue.setStop(in);
    }

    public synchronized boolean getStop() {
        return queue.getStop();
    }

    public synchronized int getDirection() {
        return direction;
    }

    public synchronized int getCurFloor() {
        return curFloor;
    }

    public synchronized int getState() {
        return state;
    }

    @Override
    public void run() {
        while (!(queue.isEmpty() && queue.getStop())) {
            PersonRequest pr = queue.getFirst();
            if (pr != null) {
                final PriorityQueue<PersonRequest> eq = new
                        PriorityQueue<>(new Comparator<PersonRequest>() {
                            @Override
                            public int compare(PersonRequest o1,
                                               PersonRequest o2) {
                                return o1.getToFloor() - o2.getToFloor();
                            }
                        });
                move(pr.getFromFloor());
                open();
                TimableOutput.println("IN-" + pr.getPersonId() +
                        "-" + curFloor);
                eq.add(pr);
                changeDir(pr.getToFloor());
                PersonRequest tmp;
                while ((tmp = queue.hasEqualFrom(pr)) != null) {
                    TimableOutput.println("IN-" + tmp.getPersonId() +
                            "-" + curFloor);
                    eq.add(tmp);
                }
                close();
                while (!eq.isEmpty()) {
                    tmp = eq.poll();
                    move(tmp.getToFloor());
                    open();
                    TimableOutput.println("OUT-" + tmp.getPersonId()
                            + "-" + curFloor);
                    while (eq.peek() != null && eq.peek().getToFloor()
                            == tmp.getToFloor()) {
                        TimableOutput.println("OUT-" + eq.poll().getPersonId()
                                + "-" + curFloor);
                    }
                    close();
                }
            }
        }
    }

    public void changeDir(int floor) {
        if (floor > curFloor) {
            this.direction = 1;
        }
        else if (floor < curFloor) {
            this.direction = -1;
        }
        else {
            this.direction = 0;
        }
    }

    public void move(int floor) {
        try {
            changeDir(floor);
            Thread.sleep(500 * Math.abs(floor - curFloor));
            this.curFloor = floor;
        } catch (InterruptedException e) {
            //e.printStackTrace();
        }
    }

    public void open() {
        try {
            TimableOutput.println("OPEN-" + curFloor);
            Thread.sleep(250);
        } catch (InterruptedException e) {
            //e.printStackTrace();
        }
    }

    public void close() {
        try {
            Thread.sleep(250);
            TimableOutput.println("CLOSE-" + curFloor);
        } catch (InterruptedException e) {
            //e.printStackTrace();
        }
    }
}
