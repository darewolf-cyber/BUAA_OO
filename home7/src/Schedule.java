import com.oocourse.elevator3.PersonRequest;

import java.util.ArrayList;
import java.util.Arrays;

public class Schedule implements Runnable {
    private static Integer[] arrA = {-3,-2,-1,1,15,16,17,18,19,20};
    private static Integer[] arrB = {-2,-1,1,2,4,5,6,7,8,9,10,11,12,13,14,15};
    private static Integer[] arrC = {1,3,5,7,9,11,13,15};
    private static ArrayList<Integer> la = new ArrayList<>(Arrays.asList(arrA));
    private static ArrayList<Integer> lb = new ArrayList<>(Arrays.asList(arrB));
    private static ArrayList<Integer> lc = new ArrayList<>(Arrays.asList(arrC));
    private Elevator eleA;
    private Elevator eleB;
    private Elevator eleC;
    private static FloorQueue<Request> outEleA;  //电梯A外的请求
    private static FloorQueue<Request> outEleB;  //电梯B外的请求
    private static FloorQueue<Request> outEleC;  //电梯C外的请求
    private static int numOfTranA = 0;
    private static int numOfTranB = 0;
    private static int numOfTranC = 0;
    private static RequestQueue<Request> queueA; //A全部请求 按顺序的
    private static RequestQueue<Request> queueB; //B全部请求 按顺序的
    private static RequestQueue<Request> queueC; //C全部请求 按顺序的
    private RequestQueue<PersonRequest> queue;

    public Schedule(RequestQueue queue) {
        this.queue = queue;
        this.outEleA = new FloorQueue();
        this.outEleB = new FloorQueue();
        this.outEleC = new FloorQueue();
        this.queueA = new RequestQueue<>();
        this.queueB = new RequestQueue<>();
        this.queueC = new RequestQueue<>();
        this.eleA = new Elevator('A',400,6,outEleA,queueA);
        this.eleB = new Elevator('B',500,8,outEleB,queueB);
        this.eleC = new Elevator('C',600,7,outEleC,queueC);
        Thread t1 = new Thread(this.eleA,"eleA");
        t1.start();
        Thread t2 = new Thread(this.eleB,"eleB");
        t2.start();
        Thread t3 = new Thread(this.eleC,"eleC");
        t3.start();
    }

    public boolean carry(Elevator ele,PersonRequest pr) {
        if ((ele.getCurFloor() < pr.getFromFloor() &&
                ele.getDirection() == 1) || (ele.getCurFloor() >
                pr.getFromFloor() && ele.getDirection() == -1) ||
                ele.getDirection() == 0 || ele.getCurFloor() ==
                pr.getFromFloor()) {
            return true;
        }
        return false;
    }

    public void selectTwo(Elevator ele1,Elevator ele2,PersonRequest pr) {
        boolean t1;
        boolean t2;
        t1 = carry(ele1,pr);
        t2 = carry(ele2,pr);
        if (t1 && t2) {
            if (!ele1.isFull() && ele2.isFull()) {
                addStright(pr,ele1.getId());
            } else if (!ele2.isFull() && ele1.isFull()) {
                addStright(pr,ele2.getId());
            } else if (!ele1.isFull() && !ele2.isFull()) {
                if (Math.abs(ele1.getCurFloor() - pr.getFromFloor()) >
                        Math.abs(ele2.getCurFloor() - pr.getFromFloor())) {
                    addStright(pr,ele2.getId());
                } else {
                    addStright(pr,ele1.getId());
                }
            } else {
                addStright(pr,ele1.getId());
            }
        } else if (t1 && !t2) {
            if (!ele1.isFull() && ele2.isFull()) {
                addStright(pr,ele1.getId());
            } else if (!ele2.isFull() && ele1.isFull()) {
                addStright(pr,ele2.getId());
            } else if (!ele1.isFull() && !ele2.isFull()) {
                addStright(pr,ele1.getId());
            } else {
                addStright(pr,ele1.getId());
            }
        } else if (!t1 && t2) {
            if (!ele1.isFull() && ele2.isFull()) {
                addStright(pr,ele1.getId());
            } else if (!ele2.isFull() && ele1.isFull()) {
                addStright(pr,ele2.getId());
            } else if (!ele1.isFull() && !ele2.isFull()) {
                addStright(pr,ele2.getId());
            } else {
                addStright(pr,ele2.getId());
            }
        } else {
            if (Math.abs(ele1.getCurFloor() - pr.getFromFloor()) >
                    Math.abs(ele2.getCurFloor() - pr.getFromFloor())) {
                addStright(pr,ele2.getId());
            } else {
                addStright(pr,ele1.getId());
            }
        }
    }

    public void selectThree(Elevator ele1,Elevator ele2,
                            Elevator ele3,PersonRequest pr) {
        boolean t1 = carry(ele1,pr);
        boolean t2 = carry(ele2,pr);
        boolean t3 = carry(ele3,pr);
        if (!t3) {
            selectTwo(ele1,ele2,pr);
        } else if (!t2) {
            selectTwo(ele1,ele3,pr);
        } else if (!t1) {
            selectTwo(ele2,ele3,pr);
        } else {
            addStright(pr,'A');
        }
    }

    public void addStright(PersonRequest pr, char ch) {
        switch (ch) {
            case 'A' : {
                Request reqa = new Request(pr.getFromFloor(),
                        pr.getToFloor(), pr.getToFloor(),
                        pr.getPersonId(), 'A', 'A');
                synchronized (queueA) {
                    queueA.add(reqa);
                    queueA.notifyAll();
                }
                synchronized (outEleA) {
                    outEleA.add(reqa.getFromFloor(), reqa);
                }
                break;
            }
            case 'B': {
                Request reqb = new Request(pr.getFromFloor(),
                        pr.getToFloor(),pr.getToFloor(),
                        pr.getPersonId(),'B','B');
                synchronized (queueB) {
                    queueB.add(reqb);
                    queueB.notifyAll();
                }
                synchronized (outEleB) {
                    outEleB.add(reqb.getFromFloor(),reqb);
                }
                break;
            }
            case 'C': {
                Request reqc = new Request(pr.getFromFloor(),
                        pr.getToFloor(), pr.getToFloor(),
                        pr.getPersonId(), 'C', 'C');
                synchronized (queueC) {
                    queueC.add(reqc);
                    queueC.notifyAll();
                }
                synchronized (outEleC) {
                    outEleC.add(reqc.getFromFloor(), reqc);
                }
                break;
            }
            default:
                break;
        }
    }

    public int solve(int i,int k,int j,int id) {
        if (la.contains(i) && la.contains(k)
                && lb.contains(k) && lb.contains(j)) {
            //System.out.println("A:"+i+"->"+k+";B:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'A','B');
            addQueue(req,'A');
            addOutFloor(req,'A');
            addNumofTran('B');
            return 1;
        }
        if (lb.contains(i) && lb.contains(k)
                && la.contains(k) && la.contains(j)) {
            //System.out.println("B:"+i+"->"+k+";A:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'B','A');
            addQueue(req,'B');
            addOutFloor(req,'B');
            addNumofTran('A');
            return 1;
        }
        if (la.contains(i) && la.contains(k)
                && lc.contains(k) && lc.contains(j)) {
            //System.out.println("A:"+i+"->"+k+";C:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'A','C');
            addQueue(req,'A');
            addOutFloor(req,'A');
            addNumofTran('C');
            return 1;
        }
        if (lc.contains(i) && lc.contains(k)
                && la.contains(k) && la.contains(j)) {
            //System.out.println("C:"+i+"->"+k+";A:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'C','A');
            addQueue(req,'C');
            addOutFloor(req,'C');
            addNumofTran('A');
            return 1;
        }
        if (lb.contains(i) && lb.contains(k)
                && lc.contains(k) && lc.contains(j)) {
            //System.out.println("B:"+i+"->"+k+";C:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'B','C');
            addQueue(req,'B');
            addOutFloor(req,'B');
            addNumofTran('C');
            return 1;
        }
        if (lc.contains(i) && lc.contains(k)
                && lb.contains(k) && lb.contains(j)) {
            //System.out.println("C:"+i+"->"+k+";B:"+k+"->"+j);
            Request req = new Request(i,k,j,id,'C','B');
            addQueue(req,'C');
            addOutFloor(req,'C');
            addNumofTran('B');
            return 1;
        }
        return 0;
    }

    public int solveOutUp(int i,int j,int id) {
        for (int l = 1; l <= 23;l++) {
            if (i - l >= -3 && i - l <= 20 && i - l != 0) {
                if (solve(i,i - l,j,id) == 1) {
                    return 1;
                }
            }
            if (j + l >= -3 && j + l <= 20 && j + l != 0) {
                if (solve(i,j + l,j,id) == 1) {
                    return 1;
                }
            }
        }
        return 0;
    }

    public int solveOutDown(int i,int j,int id) {
        for (int l = 1; l <= 23;l++) {
            if (i + l >= -3 && i + l <= 20 && i + l != 0) {
                if (solve(i,i + l,j,id) == 1) {
                    return 1;
                }
            }
            if (j - l >= -3 && j - l <= 20 && j - l != 0) {
                if (solve(i,j - l,j,id) == 1) {
                    return 1;
                }
            }
        }
        return 0;
    }

    public int solveInUp(int i,int j,int id) {
        for (int k = i + 1;k <= j - 1;k++) {
            if (k == 0) {
                continue;
            }
            if (solve(i,k,j,id) == 1) {
                return 1;
            }
        }
        return 0;
    }

    public int solveInDown(int i,int j,int id) {
        for (int k = i - 1;k >= j + 1;k--) {
            if (k == 0) {
                continue;
            }
            if (solve(i,k,j,id) == 1) {
                return 1;
            }
        }
        return 0;
    }

    public void selectEle(PersonRequest pr) {
        int i = pr.getFromFloor();
        int j = pr.getToFloor();
        boolean a = false;
        boolean b = false;
        boolean c = false;
        if (la.contains(i) && la.contains(j)) {
            //System.out.println("A:"+i+"->"+j);
            a = true;
        }
        if (lb.contains(i) && lb.contains(j)) {
            //System.out.println("B:"+i+"->"+j);
            b = true;
        }
        if (lc.contains(i) && lc.contains(j)) {
            //System.out.println("C:"+i+"->"+j);
            c = true;
        }
        if (a && !b && !c) {
            addStright(pr,'A');
        } else if (!a && b && !c) {
            addStright(pr,'B');
        } else if (!a && !b && c) {
            addStright(pr,'C');
        } else if (a && b && !c) {
            selectTwo(eleA,eleB,pr);
        } else if (a && !b && c) {
            selectTwo(eleA,eleC,pr);
        } else if (!a && b && c) {
            selectTwo(eleB,eleC,pr);
        } else if (a && b && c) {
            selectThree(eleA,eleB,eleC,pr);
        } else { //所有电梯均不能直接送达 需要换乘
            if (i < j) {
                if (solveInUp(i,j,pr.getPersonId()) == 1) {
                    return;
                }
                if (solveOutUp(i,j,pr.getPersonId()) == 1) {
                    return;
                }
            } else if (i > j) {
                if (solveInDown(i,j,pr.getPersonId()) == 1) {
                    return;
                }
                if (solveOutDown(i,j,pr.getPersonId()) == 1) {
                    return;
                }
            }
        }
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
                    selectEle(pr);
                    queue.notifyAll();
                }
            }
        }
        eleA.setStop(true);
        eleA.setnotify();
        eleB.setStop(true);
        eleB.setnotify();
        eleC.setStop(true);
        eleC.setnotify();
    }

    public static synchronized void addOutFloor(Request req, char ch) {
        switch (ch) {
            case 'A':
                synchronized (outEleA) {
                    outEleA.add(req.getFromFloor(), req);
                }
                break;
            case 'B':
                synchronized (outEleB) {
                    outEleB.add(req.getFromFloor(), req);
                }
                break;
            case 'C':
                synchronized (outEleC) {
                    outEleC.add(req.getFromFloor(), req);
                }
                break;
            default:
                break;
        }
    }

    public static synchronized void addQueue(Request req, char ch) {
        switch (ch) {
            case 'A':
                synchronized (queueA) {
                    queueA.add(req);
                    queueA.notifyAll();
                }
                break;
            case 'B':
                synchronized (queueB) {
                    queueB.add(req);
                    queueB.notifyAll();
                }
                break;
            case 'C':
                synchronized (queueC) {
                    queueC.add(req);
                    queueC.notifyAll();
                }
                break;
            default:
        }
    }

    public static synchronized void addNumofTran(char ch) {
        switch (ch) {
            case 'A':
                numOfTranA++;
                break;
            case 'B':
                numOfTranB++;
                break;
            case 'C':
                numOfTranC++;
                break;
            default:
        }
    }

    public static synchronized void subNumofTran(char ch) {
        switch (ch) {
            case 'A':
                numOfTranA--;
                break;
            case 'B':
                numOfTranB--;
                break;
            case 'C':
                numOfTranC--;
                break;
            default:
        }
    }

    public static synchronized int getNumOfTran(char ch) {
        switch (ch) {
            case 'A':
                return numOfTranA;
            case 'B':
                return numOfTranB;
            case 'C':
                return numOfTranC;
            default:
        }
        return -1;
    }
}
