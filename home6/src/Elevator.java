import com.oocourse.TimableOutput;
import com.oocourse.elevator3.PersonRequest;

import java.io.File;
import java.io.FileOutputStream;

public class Elevator implements Runnable {
    private FloorQueue inEle;   //电梯内的请求
    private FloorQueue outEle;  //电梯外的请求
    private RequestQueue queue; //全部请求 按顺序的
    private int curFloor;
    private int direction;
    private PersonRequest mainreq;
    FileOutputStream out;
    public Elevator() {
        this.inEle = new FloorQueue();
        this.outEle = new FloorQueue();
        this.queue = new RequestQueue();
        this.curFloor = 1;
        this.direction = 0;
        this.mainreq = null;
        try {
            out = new FileOutputStream(new File("E:\\res.txt"));
        }  catch (Exception e) {
            //
        }
    }

    public synchronized void outadd(PersonRequest pr) {
        outEle.add(pr.getFromFloor(),pr);
    }

    public synchronized void queueadd(PersonRequest pr) {
        queue.add(pr);
    }

    public synchronized void setStop(boolean in) {
        queue.setStop(in);
    }

    public synchronized int getDirection() {
        return direction;
    }

    public synchronized int getCurFloor() {
        return curFloor;
    }

    public synchronized void setnotify() {
        synchronized (queue) {
            queue.notifyAll();
        }
    }

    public int scanOutEle(int flag) {
        int tf = flag;
        //System.out.println("aa:"+direction+" "+mainreq+" "+inEle);
        for (PersonRequest pr : outEle.get(curFloor)) {
            if ((pr.getToFloor() > curFloor && direction == 1) ||
                    (pr.getToFloor() < curFloor && direction == -1) ||
                    pr.equals(mainreq) && inEle.isEmpty() ||
                    mainreq == null) {
                if (tf == 0) {
                    open();
                    sleep(200);
                    tf = 1;
                }
                if (pr.equals(mainreq)) {
                    changeDir(mainreq.getToFloor());
                }
                TimableOutput.println("IN-" + pr.getPersonId() + "-"
                       + curFloor);
                try {
                    out.write(("[]IN-" + pr.getPersonId() + "-" + curFloor+"\n").getBytes());
                } catch (Exception e) {
                    //
                }
                inEle.add(pr.getToFloor(),pr);
                queue.remove(pr);
                outEle.get(curFloor).remove(pr);
            }
            else if (pr.equals(mainreq) && !inEle.isEmpty()) {
                mainreq = null;
                selectMainReq();
            }
        }
        if (outEle.get(curFloor).isEmpty()) {
            outEle.remove(curFloor);
        }
        return tf;
    }

    public void scanInEle() {
        for (PersonRequest pr : inEle.get(curFloor)) {
            if (pr.equals(mainreq)) {
                mainreq = null;
                direction = 0;
            }
            TimableOutput.println("OUT-" + pr.getPersonId() + "-" + curFloor);
            try {
                out.write(("[]OUT-" + pr.getPersonId() + "-" + curFloor+"\n").getBytes());
            } catch (Exception e) {
                //
            }
        }
        inEle.remove(curFloor);
    }

    public void selectMainReq() {
        if (mainreq == null) {
            if (inEle.isEmpty()) {
                synchronized (queue) {
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
                    mainreq = queue.first();
                    if (mainreq != null) {
                        changeDir(mainreq.getFromFloor());
                    }
                }
            }
            else {
                for (int i = 0;i <= 24;i++) {
                    if (curFloor + i >= -3 && curFloor + i <= 20
                            && curFloor + i != 0) {
                        if (inEle.containsKey(curFloor + i)) {
                            mainreq = inEle.get(curFloor + i).get(0);
                            changeDir(mainreq.getToFloor());
                            break;
                        }
                    }
                    if (curFloor - i >= -3 && curFloor - i <= 20
                            && curFloor - i != 0) {
                        if (inEle.containsKey(curFloor - i)) {
                            mainreq = inEle.get(curFloor - i).get(0);
                            changeDir(mainreq.getToFloor());
                            break;
                        }
                    }
                }
            }
        }
    }
int nnn=0;
    @Override
    public void run() {
        while (true) {
            synchronized (queue) {
                if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()) {
                    break;
                }
            }
            selectMainReq();
            int flag = 0;
            if (inEle.containsKey(curFloor)) {
                open();
                flag = 1;
                sleep(200);
                scanInEle();
                if (outEle.containsKey(curFloor)) {
                    flag = scanOutEle(flag);
                }
            }
            if(nnn<100) {
                System.out.println(curFloor + " " + mainreq
                        + " " + inEle + " " + direction);
                nnn++;
            }
            if (outEle.containsKey(curFloor)) {
                flag = scanOutEle(flag);
            }
            if (flag == 1) {
                sleep(200);
                if (outEle.containsKey(curFloor)) {
                    scanOutEle(flag);
                }
                close();
            }
            if (direction != 0) {
                int re = move();
                if (re == 1) {
                    arrive();
                }
            }
        }
    }

    public int move() {
        if (direction > 0) {
            if (curFloor == 20) {
                return 0;
            }
            curFloor++;
            if (curFloor == 0) {
                curFloor++;
            }
            sleep(400);
            return 1;
        }
        else if (direction < 0) {
            if (curFloor == -3) {
                return 0;
            }
            curFloor--;
            if (curFloor == 0) {
                curFloor--;
            }
            sleep(400);
            return 1;
        }
        return 0;
    }

    public void changeDir(int floor) {
        if (floor > curFloor) {
            direction = 1;
        } else if (floor < curFloor) {
            direction = -1;
        } else {
            direction = 0;
        }
    }

    public void open() {
        TimableOutput.println("OPEN-" + curFloor);
        try {
            out.write(("[]OPEN-" + curFloor+"\n").getBytes());
        } catch (Exception e) {
            //
        }
    }

    public void close() {
        TimableOutput.println("CLOSE-" + curFloor);
        try {
            out.write(("[]CLOSE-" + curFloor+"\n").getBytes());
        } catch (Exception e) {
            //
        }
    }

    public void arrive() {
        TimableOutput.println("ARRIVE-" + curFloor);
        try {
            out.write(("[]ARRIVE-" + curFloor+"\n").getBytes());
        } catch (Exception e) {
            //
        }
    }

    public void sleep(int time) {
        try {
            Thread.sleep(time);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}
