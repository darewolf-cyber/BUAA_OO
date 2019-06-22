public class Request {
    private int fromFloor;
    private int tranFloor;
    private int toFloor;
    private int personId;
    private char firEle;
    private char secEle;

    public Request(int fromFloor, int tranFloor, int toFloor,
                   int personId, char firEle, char secEle) {
        this.fromFloor = fromFloor;
        this.tranFloor = tranFloor;
        this.toFloor = toFloor;
        this.personId = personId;
        this.firEle = firEle;
        this.secEle = secEle;
    }

    public int getFromFloor() {
        return fromFloor;
    }

    public int getTranFloor() {
        return tranFloor;
    }

    public int getToFloor() {
        return toFloor;
    }

    public int getPersonId() {
        return personId;
    }

    public char getFirEle() {
        return firEle;
    }

    public char getSecEle() {
        return secEle;
    }

    @Override
    public String toString() {
        return "Request{" +
                "fromFloor=" + fromFloor +
                ", tranFloor=" + tranFloor +
                ", toFloor=" + toFloor +
                ", personId=" + personId +
                ", firEle=" + firEle +
                ", secEle=" + secEle +
                '}';
    }
}
