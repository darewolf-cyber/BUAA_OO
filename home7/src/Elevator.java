import com.oocourse.TimableOutput;

public class Elevator implements Runnable {
    private FloorQueue<Request> inEle;   //电梯内的请求
    private FloorQueue<Request> outEle;  //电梯外的请求
    private RequestQueue<Request> queue; //全部请求 按顺序的
    private int curFloor;
    private int direction;
    private Request mainreq;
    private char id;
    private int moveTime;
    private int maxNum;
    private int curNum;

    public Elevator(char id,int moveTime,int maxNum,
                    FloorQueue<Request> outEle,RequestQueue<Request> queue) {
        this.id = id;
        this.moveTime = moveTime;
        this.maxNum = maxNum;
        this.curNum = 0;
        this.curFloor = 1;
        this.direction = 0;
        this.mainreq = null;
        this.inEle = new FloorQueue();
        this.outEle = outEle;
        this.queue = queue;
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

    public char getId() {
        return id;
    }

    public int getCurNum() {
        return curNum;
    }

    public boolean isFull() {
        synchronized (queue) {
            return (queue.size() == maxNum) || (curNum == maxNum);
        }
        //return curNum  == maxNum;
    }

    public boolean isEmpty() {
        return curNum == 0;
    }

    public Request getMainreq() {
        return mainreq;
    }

    public synchronized void setnotify() {
        synchronized (queue) {
            queue.notifyAll();
        }
    }

    public int scanOutEle(int flag) {
        int tf = flag;
        //System.out.println("aa:"+direction+" "+mainreq+" "+inEle);
        for (Request pr : outEle.get(curFloor)) {
            if (curNum == maxNum) {
                if (outEle.get(curFloor).contains(mainreq)) {
                    mainreq = null;
                    selectMainReq();
                }
                break;
            }
            if ((pr.getTranFloor() > curFloor && direction == 1) ||
                    (pr.getTranFloor() < curFloor && direction == -1) ||
                    pr.equals(mainreq) && inEle.isEmpty() ||
                    mainreq == null) {
                if (tf == 0) {
                    open();
                    sleep(200);
                    tf = 1;
                }
                if (pr.equals(mainreq)) {
                    changeDir(mainreq.getTranFloor());
                }
                synchronized (TimableOutput.class) {
                    TimableOutput.println("IN-" + pr.getPersonId() + "-"
                            + curFloor + "-" + id);
                }
                inEle.add(pr.getTranFloor(),pr);
                curNum++;
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
        for (Request pr : inEle.get(curFloor)) {
            if (pr.equals(mainreq)) {
                mainreq = null;
                direction = 0;
            }
            synchronized (TimableOutput.class) {
                TimableOutput.println("OUT-" + pr.getPersonId() + "-"
                        + curFloor + "-" + id);
            }
            curNum--;
            if (pr.getTranFloor() != pr.getToFloor()) {
                Request req = new Request(pr.getTranFloor(),pr.getToFloor(),
                        pr.getToFloor(),pr.getPersonId(), pr.getSecEle(),
                        pr.getSecEle());
                Schedule.addOutFloor(req,pr.getSecEle());
                Schedule.addQueue(req,pr.getSecEle());
                Schedule.subNumofTran(pr.getSecEle());
                //System.out.println(req);
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
                            changeDir(mainreq.getTranFloor());
                            break;
                        }
                    }
                    if (curFloor - i >= -3 && curFloor - i <= 20
                            && curFloor - i != 0) {
                        if (inEle.containsKey(curFloor - i)) {
                            mainreq = inEle.get(curFloor - i).get(0);
                            changeDir(mainreq.getTranFloor());
                            break;
                        }
                    }
                }
            }
        }
    }

    @Override
    public void run() {
        while (true) {
            synchronized (queue) {
                if (queue.isEmpty() && queue.getStop() && inEle.isEmpty()
                        && Schedule.getNumOfTran(id) == 0) {
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
            //System.out.println(id+" "+curFloor + " " + mainreq
            //        + " " + inEle + " " + direction);
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
        //System.err.println("!!!!!!!!!!!!!!!!!!!!!!!!!"+id+" is end");
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
            sleep(moveTime);
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
            sleep(moveTime);
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
        synchronized (TimableOutput.class) {
            TimableOutput.println("OPEN-" + curFloor + "-" + id);
        }
    }

    public void close() {
        synchronized (TimableOutput.class) {
            TimableOutput.println("CLOSE-" + curFloor + "-" + id);
        }
    }

    public void arrive() {
        synchronized (TimableOutput.class) {
            TimableOutput.println("ARRIVE-" + curFloor + "-" + id);
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
